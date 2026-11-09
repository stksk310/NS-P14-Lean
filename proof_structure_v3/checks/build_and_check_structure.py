#!/usr/bin/env python3
"""Assemble the V03 architecture and check declared structure, not mathematics."""

from collections import Counter
import hashlib
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[2]
BASE = ROOT / "proof_structure_v3"
WORK = BASE / "work"


def require(condition, message):
    if not condition:
        raise ValueError(message)


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def words(value):
    if isinstance(value, list):
        return "；".join(words(x) for x in value)
    return str(value)


def source_role(entry, source):
    path = source["path"]
    if entry["kind"] == "published":
        return "適用statementの登録（完全証明は公刊原典）"
    if path.endswith(".py"):
        return "厳密算術の検算補助"
    if any(term in path for term in ["audit", "REFEREE", "REVIEW", "READABILITY"]):
        return "内部監査・途中式の補助展開"
    if path.startswith("proof_structure_v3/"):
        return "今回の骨子・合成（全文の代替ではない）"
    if entry["kind"] == "standard_algebra":
        return "通常の基礎代数の使用宣言"
    return "保存された完全証明"


def preserve_sources():
    receipt = json.loads((BASE / "SOURCE_RECEIPT.json").read_text())
    counts = {}
    for folder, record in receipt["preserved_packages"].items():
        base = ROOT / folder
        require(digest(base / record["manifest"]) == record["manifest_sha256"],
                ("changed source manifest", folder))
        for path, expected in record["members"].items():
            require(digest(base / path) == expected, ("changed source", folder, path))
        counts[folder] = len(record["members"])
    spec = receipt["spec"]
    require(digest(ROOT / spec["local_path"]) == spec["sha256"], "changed input brief")
    return counts


def tag_requests(value):
    """Interpret only explicit labels/ranges; retain prose pointers for humans."""
    value = value.replace("(", "").replace(")", "").strip()
    interval = re.fullmatch(r"([A-Z]+)(\d+)[–−-]([A-Z]+)(\d+)", value)
    if interval:
        prefix, lo, other, hi = interval.groups()
        require(prefix == other and int(lo) <= int(hi), ("bad label range", value))
        return [prefix + str(i) for i in range(int(lo), int(hi) + 1)]
    if re.fullmatch(r"(?:[A-Z]+[.\d][.\d]*|\d+(?:\.\d+)?|H|TAR|TMIN|ORD|TLOW|V3-MAIN)", value):
        return [value]
    return []


def main():
    preserved = preserve_sources()
    fragments = [
        "INTRO_AND_PART_I.md", "ORDINARY_PARTS.md", "ENDPOINT_PART.md",
        "WIDTH_PART.md", "PART_VI.md",
    ]
    manuscript = "\n\n".join((WORK / name).read_text().strip() for name in fragments) + "\n"
    (BASE / "P14_PROOF_SKELETON_V03_JA.md").write_text(manuscript)
    entries = []
    for name in ["common_registry.json", "ordinary_registry.json",
                 "endpoint_registry.json", "width_registry.json"]:
        entries.extend(json.loads((WORK / name).read_text()))
    ids = [entry["id"] for entry in entries]
    require(len(ids) == len(set(ids)), "duplicate lemma ID")
    table = {entry["id"]: entry for entry in entries}
    required = {"id", "part", "title", "statement", "quantifiers", "assumptions",
                "depends_on", "proof_core", "sources", "kind", "characteristic", "audit"}
    source_files = set()
    checked_tags = 0
    descriptive_pointers = 0
    for entry in entries:
        name = entry["id"]
        require(required <= entry.keys(), ("missing lemma fields", name))
        for key in required - {"depends_on"}:
            require(entry[key], ("empty lemma field", name, key))
        require(isinstance(entry["depends_on"], list), ("dependency type", name))
        require(set(entry["depends_on"]) <= table.keys(), ("unknown dependency", name))
        require(len(entry["depends_on"]) == len(set(entry["depends_on"])),
                ("duplicate direct input", name))
        require({"status", "evidence", "limits"} <= entry["audit"].keys(),
                ("audit scope fields", name))
        for source in entry["sources"]:
            path = ROOT / source["path"]
            require(path.is_file(), ("missing proof source", name, path))
            source_files.add(source["path"])
            tags = set(re.findall(r"\\tag\{([^}]+)\}", path.read_text()))
            require(source.get("section"), ("source section absent", name))
            for pointer in source.get("equations", []):
                requests = tag_requests(pointer)
                if not requests:
                    descriptive_pointers += 1
                for label in requests:
                    require(label in tags, ("equation label not in source", name, str(path), label))
                    checked_tags += 1

    state, order = {}, []

    def visit(name):
        require(state.get(name) != 1, ("dependency cycle", name))
        if state.get(name) == 2:
            return
        state[name] = 1
        for dep in table[name]["depends_on"]:
            visit(dep)
        state[name] = 2
        order.append(name)

    visit("I_MAIN")
    require(set(order) == set(ids), ("orphan declared lemmas", sorted(set(ids) - set(order))))
    entries = [table[name] for name in order]
    payload = {"root": "I_MAIN", "direction": "conclusion -> direct mathematical inputs",
               "scope": "Declared proof architecture; acyclicity is not a proof of lemma truth.",
               "lemmas": entries}
    (BASE / "lemma_registry.json").write_text(json.dumps(payload, ensure_ascii=False, indent=2) + "\n")

    direct_redundancies = []

    def ancestors(name):
        answer = set()
        for dep in table[name]["depends_on"]:
            answer.add(dep)
            answer.update(ancestors(dep))
        return answer

    for name in order:
        deps = table[name]["depends_on"]
        for dep in deps:
            via = [other for other in deps if other != dep and dep in ancestors(other)]
            if via:
                direct_redundancies.append({"lemma": name, "input": dep, "also_via": via})

    lines = [
        "# P14 証明依存関係 V03", "",
        "主定理 I_MAIN から逆向きに追う。各補題のstatement・量化・仮定・先行依存・核心・",
        "完全証明の所在・入力種別・任意標数性・監査状態を記録する。",
        "この表と lemma_registry.json は同じデータから生成する。", "",
        "## 選択したルートと除外した依存", "",
        "- ordinaryはO_LOW/O_SMALL/O_LARGE。actual Apéry–Sidonを使い、旧第15節の全系統を主依存から外す。",
        "- narrowはE_TRANSFERを共通基礎にW_CLOSE/N_CLOSE。N4の第一行だけ紙上置換し、高次行と幅4は保持する。",
        "- 旧196組、旧83組・665比較・5tail、Navi別証明はこのグラフの頂点・前提に含まない。",
        "- BHP/EKは幅側dense評価に残る。旧ordinary lexの除外から公刊入力まで消したとはしない。",
        "- X_*は公刊入力又は通常の基礎代数。各出典の監査記録は公刊定理の再証明やLean認証ではない。", "",
        "## 主定理からの逆引き", "",
        "| 補題ID | 役割 | 直接の数学的入力 |",
        "|---|---|---|",
    ]
    for entry in reversed(entries):
        deps = ", ".join(entry["depends_on"]) or "外部・基礎入力"
        lines.append(f"| {entry['id']} | {entry['title']} | {deps} |")
    lines.extend(["", "## 全補題の精密な記録", ""])
    for entry in entries:
        name = entry["id"]
        lines.extend([f"### {name}：{entry['title']}", ""])
        fields = [
            ("配置", entry["part"]), ("正確なstatement", entry["statement"]),
            ("量化範囲", entry["quantifiers"]), ("仮定", entry["assumptions"]),
            ("先行依存", ", ".join(entry["depends_on"]) or "外部・通常の基礎入力"),
            ("証明の核心", entry["proof_core"]),
        ]
        for title, value in fields:
            lines.append(f"- **{title}：** {words(value)}")
        for source in entry["sources"]:
            path = ROOT / source["path"]
            suffix = "、".join(source.get("equations", []))
            role = source_role(entry, source)
            lines.append(f"- **{role}：** [{source['path']}]({path}) {source['section']}；{suffix}")
        if entry.get("published_reference"):
            reference = entry["published_reference"]
            lines.append(f"- **公刊原典：** [{reference['title']}]({reference['url']}) {reference['locator']}")
        if entry.get("source_scope"):
            lines.append(f"- **引用する範囲：** {entry['source_scope']}")
        lines.extend([
            f"- **入力種別：** {entry['kind']}",
            f"- **任意標数性：** {entry['characteristic']}",
            f"- **現在の監査：** {words(entry['audit']['status'])}",
            f"- **監査根拠：** {words(entry['audit']['evidence'])}",
            f"- **監査の限界：** {words(entry['audit']['limits'])}", "",
        ])
    lines.extend([
        "## 共通入力と重複の区別", "",
        "ordinaryとnarrowは数値座標、Koszul/Tor、actual targetを共有するが、塔・端点模型を相互に依存させない。",
        "X_BASIC等が複数の補題に現れるのは、その局所証明でも使う入力を明示するためである。",
        "直接依存には推移的に重なる辺がある。これは新しい仮定や循環ではない。",
        "機械的な推移簡約は可能だが、各局所証明が直接使う仮定を隠さない表記を採用した。",
        f"構造点検は{len(entries)}頂点、{sum(len(v['depends_on']) for v in entries)}辺の非循環性と主定理からの到達性を確認する。",
        "その検査は、statementの数学的な正しさを自動認証するものではない。", "",
        "## 出典の旧結論を継承しない範囲", "",
        "I_MAINはV03 Part VIで新しく合成する。旧V02§16の旧§15呼出しを前提として継承しない。",
        "N_WIDTH4はV02§14.6 N23–N28と全multiplicity比較のみを使う。同節末尾の196組を使う全域結論は使わない。",
        "N_CLOSEは紙上の新第一行と保持したN_HIGH/N_WIDTH4から再合成する。",
    ])
    (BASE / "P14_DEPENDENCY_MAP_V03.md").write_text("\n".join(lines) + "\n")

    coverage = {
        "small_embedding": {"e=1,2": "I_BASE", "e=3": "I_THREE"},
        "ordinary": {"scope": "e>=4,w>=m-1",
                     "rank2,3": "O_LOW", "rank4..8": "O_SMALL", "rank>=9": "O_LARGE",
                     "delta=0": "O_LOW (empty tower)", "top_relative_rank": "O_TOR,O_SCALAR,O_TARGET"},
        "narrow": {"scope": "e>=4,w<=m-2,m>=du+2",
                   "e=4": {"u=3,4": "N_SMALL,N_WIDTH4", "u=5": "N_FIRST",
                           "u=6,7,8": "N_SMALL", "u>=9": "N_FIRST", "rows2..4": "N_HIGH"},
                   "e=5": {"u=4,5": "W_EDGE", "u=6,7,u>=8": "W_FIVE"},
                   "e>=6": {"u=e-1,e": "W_EDGE", "e+1<=u<=2e-3": "W_DENSE",
                            "u>=2e-2": "W_SPARSE"}},
        "boundary_w=m-1": "ordinary",
        "all_fields": "I_FIELD for ordinary cut; each narrow lemma over the given field",
        "all_rows": "row0=1; retained top rows; i>e source0",
        "verification_scope": "This records the mathematical coverage argument; no finite parameter sweep proves universal coverage.",
    }
    (BASE / "COVERAGE_V03.json").write_text(json.dumps(coverage, ensure_ascii=False, indent=2) + "\n")
    for r in range(2, 100):
        require(sum([r in (2, 3), 4 <= r <= 8, r >= 9]) == 1,
                "rank partition transcription")
    for e in range(6, 30):
        for u in range(e - 1, 3 * e):
            require(sum([u in (e - 1, e), e + 1 <= u <= 2 * e - 3, u >= 2 * e - 2]) == 1,
                    "width partition transcription")
    # These small integer checks only detect transcription of the displayed intervals.
    document_paths = [
        BASE / "P14_PROOF_SKELETON_V03_JA.md", BASE / "P14_DEPENDENCY_MAP_V03.md",
        BASE / "P14_PROOF_REPLACEMENT_LEDGER_V03.md", BASE / "P14_REFEREE_READINESS_V03.md",
    ]
    local_links = 0
    for path in document_paths:
        content = path.read_text()
        require(not any(ord(c) < 32 and c not in "\n\r\t" for c in content),
                ("control character", path))
        require(content.count(r"\(") == content.count(r"\)"), ("inline math", path))
        require(content.count(r"\[") == content.count(r"\]"), ("display math", path))
        for raw in re.findall(r"\]\((<[^>]+>|[^)\s]+)\)", content):
            href = raw.strip("<>")
            if href.startswith(("http://", "https://", "#")):
                continue
            stem = re.sub(r":\d+$", "", href)
            target = Path(stem) if stem.startswith("/") else path.parent / stem
            require(target.exists(), ("missing local link", path, href))
            local_links += 1
    labels = re.findall(r"\\tag\{([^}]+)\}", manuscript)
    duplicates = [label for label, count in Counter(labels).items() if count > 1]
    require(not duplicates, ("duplicate skeleton equation tags", duplicates))
    report = {
        "status": "PASS_DECLARED_ARCHITECTURE_STRUCTURE",
        "lemma_nodes": len(entries), "dependency_edges": sum(len(v["depends_on"]) for v in entries),
        "acyclic": True, "all_nodes_reachable_from_main": True,
        "topological_order": order,
        "transitively_repeated_local_inputs": direct_redundancies,
        "referenced_source_files": sorted(source_files),
        "explicit_equation_labels_checked": checked_tags,
        "descriptive_equation_pointers_for_human_review": descriptive_pointers,
        "preserved_source_members": preserved,
        "four_required_outputs_local_links_checked": local_links,
        "skeleton_equation_tags": len(labels), "duplicate_tags": duplicates,
        "coverage": coverage,
        "scope_limit": "Hashes, references, declared DAG, intervals, delimiters. Not semantic proof checking, external peer review, or Lean kernel verification.",
    }
    (BASE / "audits/STRUCTURE_CHECK.json").write_text(json.dumps(report, ensure_ascii=False, indent=2) + "\n")
    print(json.dumps({key: value for key, value in report.items()
                      if key not in {"transitively_repeated_local_inputs", "coverage", "topological_order"}},
                     ensure_ascii=False, indent=2))


if __name__ == "__main__":
    main()
