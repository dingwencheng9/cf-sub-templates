"""组装分流规则集：把上游分类文件合成 direct / proxy / reject / fake-ip-filter 四层。

为什么是独立脚本而不是 YAML 内联
--------------------------------
这段逻辑有真实的分支与阈值判断（校验、剔除、冲突消解、规模下限）。
内联在 workflow 的 heredoc 里既没法在 CI 之外复现验证，也没法写单测——
改坏了只能靠等 CI 跑一次才知道。抽成脚本后：

* 本地可以用真实上游数据直接跑一遍验证（本次就是这么验的）；
* workflow 里只剩"拉取 -> 调用 -> 发布"三步，逻辑集中在一处；
* 校验失败时脚本以非零码退出，workflow 的 ``rules/`` 保持旧内容不变。

输入
----
``RULE_CACHE`` 指向的目录里放上游的 ``<category>.list`` 原始文件。

输出
----
``RULE_OUT`` 指向的目录里产出 ``direct.txt`` / ``proxy.txt`` /
``reject.txt`` / ``fake_ip_filter.txt`` / ``meta.json`` / ``manifest.json``。

格式约定
--------
每行一个 mihomo DOMAIN 表达式，统一写成 ``+.<body>``。

统一前缀**不改变行为**：mihomo 的 ``DOMAIN-SUFFIX`` 对裸域与 ``+.``
前缀语义相同（主仓库 ``cf_rules.render_domain_rules`` 渲染前一律
strip 前缀）。但统一之后，"同一域名两种写法"（``cdn.angruo.com`` 与
``+.cdn.angruo.com``）在集合层面就是同一个元素，跨层冲突才能被
真正消解掉——否则字符串层看不出的冲突会一路带进渲染结果。

上游来源
--------
MetaCubeX/meta-rules-dat 的 ``meta`` 分支：

* ``geo-lite/geosite/<category>.list`` —— 分类集（geo-lite 是精简版，
  每个分类只有一条 ``.list``，与本项目的用��场景匹配）；
* ``geo/geosite/category-ads-all.list`` —— 广告分类，**只在 geo/ 下有**，
  geo-lite/ 里没有。

上游**不提供任何 checksum 文件**，因此"下载到的内容是否被篡改"无法靠
上游校验；唯一的可靠办法是把 commit sha 记进 ``meta.json``，让每一行
都能追溯到具体的上游快照。产物的 sha256 由本脚本自己算并写入。
"""

from __future__ import annotations

import hashlib
import json
import os
import re
import sys
from datetime import datetime, timezone
from pathlib import Path

CACHE = Path(os.environ.get("RULE_CACHE", ".cache/rules"))
OUT = Path(os.environ.get("RULE_OUT", ".cache/out"))

# 各层取自哪些上游分类
DIRECT_CATS = ["cn", "apple", "applemusic", "bilibili"]
PROXY_CATS = ["proxy", "google", "youtube", "github", "openai"]
REJECT_CATS = ["category-ads-all"]
FAKEIP_CATS = ["private"]

# 各层的规模下限。上游某天分类结构变了或拉到了残缺文件时，
# 规模会异常下跌——宁可整个 job 失败（旧规则集原样保留），
# 也不要让一套残缺的规则集顶替掉好用的。
MIN_COUNTS = {"direct": 1000, "proxy": 500, "reject": 100, "fake_ip_filter": 20}

# reject 层误伤 direct 层的上限比例。超过说明上游分类错位了
# （比如广告分类混进了国内域名），同样应当失败而不是发布。
REJECT_OVER_DIRECT_MAX_RATIO = 0.05

# 哈希样式 CDN 随机子域，例如 0gr4uqmtt8y41hcjsgrzdrc31.ourdvsss.com
JUNK = re.compile(r"^[a-z0-9]{20,}\.[a-z0-9.-]+$")

stats_excluded = {"arpa": 0, "junk": 0, "invalid": 0, "duplicate": 0}
cat_items: dict[str, list[str]] = {}
cat_bad: dict[str, list[dict]] = {}


def strip_wildcard(expr: str) -> str:
    """去掉 ``+.`` / ``*.`` 前缀，返回域名主体。"""
    for prefix in ("+.", "*."):
        if expr.startswith(prefix):
            return expr[len(prefix):]
    return expr


def valid_expr(expr: str) -> bool:
    """校验一个 mihomo DOMAIN 表达式。

    与主仓库 ``cf_rules._is_valid_expression`` 相比有**两处放宽**，
    两处都必要：

    1. **接受单标签 TLD**（``+.cn`` / ``+.ms`` / ``+.lan``）。
       上游 ``cn.list`` 里确实有 ``+.cn``——丢掉它意味着丢掉整个
       ``.cn`` 顶级域的直连覆盖，是静默的覆盖率损失。
       纯裸单标签（``cn``）仍然拒绝：那不是 TLD 表达式，是主机名。

    2. **接受 IDN Punycode 顶级域**（``xn--fiqs8s`` 等）。
       上游 cn/apple 分类里有 14 条这类条目，旧的"顶级域必须是纯字母"
       规则会把它们全部误杀——其中 ``xn--fiqs8s`` 就是中文 ``.中国``。
    """
    if not expr or len(expr) > 128:
        return False
    if any(ch in expr for ch in " /\t:@?#"):
        return False
    body, wildcard = expr, False
    for prefix in ("+.", "*."):
        if body.startswith(prefix):
            body, wildcard = body[len(prefix):], True
            break
    if not body:
        return False
    labels = body.split(".")
    if any(not label or len(label) > 63 for label in labels):
        return False
    if not all(ch.isalnum() or ch == "-" for ch in "".join(labels)):
        return False
    tld = labels[-1]
    if tld.startswith("xn--"):
        # Punycode 顶级域：xn-- 后必须跟至少一个 ASCII 字母数字
        if len(tld) <= 4 or not tld[4:].isascii() or not tld[4:].isalnum():
            return False
    elif not (tld.isalpha() and len(tld) >= 2):
        return False
    if wildcard and len(labels) == 1:
        return True
    return len(labels) >= 2


def is_arpa(expr: str) -> bool:
    """反向解析域名——不是分流需求。"""
    body = strip_wildcard(expr)
    return body == "arpa" or body.endswith(".arpa")


def is_junk(expr: str) -> bool:
    """哈希样式 CDN 随机子域。"""
    return bool(JUNK.match(strip_wildcard(expr)))


def load_category(cat: str) -> list[str]:
    """读取一个上游分类文件，返回校验通过的条目列表。"""
    path = CACHE / f"{cat}.list"
    if not path.exists():
        sys.exit(f"[FATAL] 缺少上游文件: {path}")
    try:
        raw = path.read_text(encoding="utf-8")
    except OSError as exc:
        sys.exit(f"[FATAL] 上游文件读取失败: {path} ({exc})")

    items: list[str] = []
    bad: list[dict] = []
    seen: set[str] = set()
    for lineno, line in enumerate(raw.splitlines(), start=1):
        line = line.strip()
        if not line or line.startswith("#"):
            continue
        if "#" in line:
            line = line.split("#", 1)[0].strip()
            if not line:
                continue
        if not valid_expr(line):
            bad.append({"line": lineno, "expr": line})
            continue
        if line in seen:
            stats_excluded["duplicate"] += 1
            continue
        seen.add(line)
        items.append(line)
    cat_bad[cat] = bad
    stats_excluded["invalid"] += len(bad)
    return items


def clean(items: list[str]) -> list[str]:
    """剔除 arpa 与哈希样式垃圾条目。"""
    out: list[str] = []
    for expr in items:
        if is_arpa(expr):
            stats_excluded["arpa"] += 1
            continue
        if is_junk(expr):
            stats_excluded["junk"] += 1
            continue
        out.append(expr)
    return out


def union(cats: list[str]) -> list[str]:
    """并集（保持分类内原有顺序）。"""
    out: list[str] = []
    seen: set[str] = set()
    for cat in cats:
        for expr in cat_items[cat]:
            if expr not in seen:
                seen.add(expr)
                out.append(expr)
    return out


def normalize(items: list[str]) -> list[str]:
    """按域名主体归一化，输出统一形态（裸 body，排序输出）。

    归一化后同一个域名无论上游写成 ``a.com`` 还是 ``+.a.com``，
    都是同一个字符串——跨层冲突得以在集合层面被真正消解。
    """
    seen: set[str] = set()
    for expr in items:
        seen.add(strip_wildcard(expr))
    return sorted(seen)


def sha256_of(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def write_layer(name: str, bodies: list[str]) -> Path:
    """写出一层规则，每行一个 ``+.<body>``。"""
    path = OUT / name
    path.write_text("".join(f"+.{body}\n" for body in bodies), encoding="utf-8")
    return path


def main() -> int:
    OUT.mkdir(parents=True, exist_ok=True)

    for cat in DIRECT_CATS + PROXY_CATS + REJECT_CATS + FAKEIP_CATS:
        cat_items[cat] = clean(load_category(cat))

    direct = normalize(union(DIRECT_CATS))
    proxy = normalize(union(PROXY_CATS))
    reject = normalize(union(REJECT_CATS))
    fakeip = normalize(union(FAKEIP_CATS))

    # ---- 层间冲突消解：显式优先级，不靠渲染顺序的偶然结果 ----
    #
    # 优先级 reject > direct > proxy，与主仓库 mihomo 的渲染顺序一致
    # （约束 155：reject → direct → proxy）。规则是顺序匹配、首个命中
    # 即生效，所以这个顺序必须写在数据里，而不是留给渲染时的巧合。
    reject_set = set(reject)
    over_reject = [b for b in direct if b in reject_set]
    over_reject += [b for b in proxy if b in reject_set]
    direct = [b for b in direct if b not in reject_set]
    proxy = [b for b in proxy if b not in reject_set]

    direct_set = set(direct)
    over_direct = [b for b in proxy if b in direct_set]
    proxy = [b for b in proxy if b not in direct_set]

    counts = {
        "direct": len(direct),
        "proxy": len(proxy),
        "reject": len(reject),
        "fake_ip_filter": len(fakeip),
    }

    # ---- 校验：不过就整体失败，rules/ 保持旧内容 ----
    for layer, minimum in MIN_COUNTS.items():
        if counts[layer] < minimum:
            sys.exit(
                f"[FATAL] {layer} 层只有 {counts[layer]} 条，低于下限 {minimum}"
                "——上游可能异常或分类结构已变"
            )
    if over_reject and len(over_reject) > len(direct) * REJECT_OVER_DIRECT_MAX_RATIO:
        sys.exit(
            f"[FATAL] reject 层误伤 direct 层 {len(over_reject)} 条"
            f"（>{REJECT_OVER_DIRECT_MAX_RATIO:.0%}）——上游分类可能错位"
        )
    if set(direct) & set(proxy):
        sys.exit("[FATAL] direct 与 proxy 仍有交集——冲突消解失效")

    # ---- 落盘 ----
    files = {
        "direct.txt": write_layer("direct.txt", direct),
        "proxy.txt": write_layer("proxy.txt", proxy),
        "reject.txt": write_layer("reject.txt", reject),
        "fake_ip_filter.txt": write_layer("fake_ip_filter.txt", fakeip),
    }

    layers = {
        "direct": {
            "categories": DIRECT_CATS,
            "count": counts["direct"],
            "sha256": sha256_of(files["direct.txt"]),
        },
        "proxy": {
            "categories": PROXY_CATS,
            "count": counts["proxy"],
            "sha256": sha256_of(files["proxy.txt"]),
        },
        "reject": {
            "categories": REJECT_CATS,
            "count": counts["reject"],
            "sha256": sha256_of(files["reject.txt"]),
        },
        "fake_ip_filter": {
            "categories": FAKEIP_CATS,
            "count": counts["fake_ip_filter"],
            "sha256": sha256_of(files["fake_ip_filter.txt"]),
        },
    }

    # 本地权威层（主仓库 config/rule_domains/local_*.txt）如果也在本仓库，
    # 记录其 sha256——同步时不动它们，只留痕。
    local_layer: dict[str, dict] = {}
    for name in (
        "local_direct.txt",
        "local_proxy.txt",
        "local_reject.txt",
        "local_fake_ip_filter.txt",
    ):
        path = Path("rules") / name
        if path.exists():
            local_layer[name] = {
                "sha256": sha256_of(path),
                "bytes": path.stat().st_size,
            }

    meta = {
        "schema_version": 2,
        "generated_at": datetime.now(timezone.utc).isoformat(timespec="seconds"),
        "source": {
            "repo": "MetaCubeX/meta-rules-dat",
            "branch": "meta",
            "commit": os.environ.get("UPSTREAM_SHA", "unknown"),
            "layout": {
                "geo-lite": "geo-lite/geosite/{category}.list",
                "ads": "geo/geosite/category-ads-all.list",
            },
            "note": (
                "上游不提供 checksum 文件；本文件记录的 commit 为实际拉取到的上游快照，"
                "各层 sha256 为本地产物校验值。"
            ),
        },
        "layers": layers,
        "local_layer": local_layer,
        "excluded": {
            "arpa": "反向解析域名（in-addr.arpa / ip6.arpa），不是真实分流需求",
            "junk": "哈希样式 CDN 随机子域（长随机首段），上游 bilibili 等分类存在此类",
            "invalid": "未通过表达式校验的行（数量见 invalid_samples）",
            "reject_over_direct": "reject 层误伤 direct 层的条目（广告域名同时出现在国内分类）",
            "direct_over_proxy": "direct 层与 proxy 层语义重合的条目，按 direct > proxy 消解",
        },
        "excluded_stats": stats_excluded,
        "invalid_samples": {c: b[:5] for c, b in cat_bad.items() if b},
        "conflicts_resolved": {
            "priority": "reject > direct > proxy",
            "reject_over_direct": len(over_reject),
            "reject_over_direct_samples": over_reject[:20],
            "direct_over_proxy": len(over_direct),
            "direct_over_proxy_samples": over_direct[:20],
        },
        "totals": counts,
    }
    (OUT / "meta.json").write_text(
        json.dumps(meta, ensure_ascii=False, indent=2) + "\n", encoding="utf-8"
    )

    # manifest 最后写：它是"这套规则集是否完整"的唯一入口。
    manifest = {
        "schema_version": 1,
        "generated_at": meta["generated_at"],
        "source": meta["source"],
        "files": {
            name: {"sha256": sha256_of(path), "count": layers[name[: -len(".txt")]]["count"]}
            for name, path in files.items()
        },
        "meta": {"sha256": sha256_of(OUT / "meta.json")},
    }
    (OUT / "manifest.json").write_text(
        json.dumps(manifest, ensure_ascii=False, indent=2) + "\n", encoding="utf-8"
    )

    print("层规模:", json.dumps(counts, ensure_ascii=False))
    print("剔除:", json.dumps(stats_excluded, ensure_ascii=False))
    print(
        "冲突消解: reject>direct =",
        len(over_reject),
        ", direct>proxy =",
        len(over_direct),
    )
    print("残余交集:", len(set(direct) & set(proxy)))
    return 0


if __name__ == "__main__":
    sys.exit(main())
