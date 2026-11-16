#!/usr/bin/env python3
"""Check planning coverage and accounting; this does not check Lean proofs."""

from collections import Counter
import hashlib
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[2]
BASE = ROOT / "lean_planning"


def require(condition, detail):
    if not condition:
        raise ValueError(detail)


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    plan = json.loads((BASE / "modules.json").read_text())
    source_path = ROOT / plan["source_registry"]
    require(sha(source_path) == plan["source_registry_sha256"], "registry changed")
    registry = json.loads(source_path.read_text())["lemmas"]
    ids = {entry["id"] for entry in registry}
    modules = {entry["id"]: entry for entry in plan["modules"]}
    require(len(modules) == 18, "module count")
    owners = {}
    for name, module in modules.items():
        for lemma in module["primary_registry_ids"]:
            require(lemma not in owners, ("duplicate owner", lemma))
            owners[lemma] = name
    require(set(owners) == ids, ("mapping coverage", set(owners) ^ ids))
    require(owners == plan["registry_id_to_module"], "mapping tables disagree")
    quotient = {(owners[entry["id"]], owners[dep])
                for entry in registry for dep in entry["depends_on"]
                if owners[entry["id"]] != owners[dep]}
    recorded = {(edge["dependent"], edge["prerequisite"])
                for edge in plan["registry_quotient_edges"]}
    require(quotient == recorded, "registry quotient edges")
    edges = quotient | {(edge["dependent"], edge["prerequisite"])
                        for edge in plan["planned_interface_edges"]}
    require(all(a in modules and b in modules for a, b in edges), "unknown module")
    state = {}

    def visit(name):
        require(state.get(name) != 1, ("module cycle", name))
        if state.get(name) == 2:
            return
        state[name] = 1
        for a, b in edges:
            if a == name:
                visit(b)
        state[name] = 2

    for name in modules:
        visit(name)
    published = {entry["id"] for entry in registry if entry["kind"] == "published"}
    require(len(published) == 7, "published roots")
    require({row["registry_id"] for row in plan["published_inputs"]} == published,
            "published mapping")
    require(all(row["proof_required"] and not row["axiom_wrapper_is_completion"]
                for row in plan["published_inputs"]), "published proof boundary")
    low = sum(m["effort_person_days"]["lower"] for m in modules.values())
    high = sum(m["effort_person_days"]["upper"] for m in modules.values())
    require((low, high) == (918, 2620), "module effort")
    require((low + 2, high + 5) == (920, 2625), "setup accounting")
    grouped = [(235, 660), (380, 1120), (130, 345), (70, 190), (95, 280), (8, 25)]
    require(tuple(map(sum, zip(*grouped))) == (low, high), "group accounting")
    main_text = (BASE / "P14_LEAN_FORMALIZATION_PLAN_JA.md").read_text()
    for name, module in modules.items():
        budget = module["effort_person_days"]
        require(len(re.findall(r"^\| " + name + r" \|", main_text, re.M)) == 1,
                ("module row count", name))
        row = re.search(r"^\| " + name + r" \|.*$", main_text, re.M).group(0)
        require(f"{budget['lower']}–{budget['upper']}人日" in row,
                ("budget transcription", name))
    preserve = json.loads((ROOT / "proof_structure_v3/MANIFEST_SHA256.json").read_text())
    for path, digest in preserve.items():
        require(sha(ROOT / "proof_structure_v3" / path) == digest,
                ("changed V03 member", path))
    inventory = json.loads((BASE / "mathlib_inventory.json").read_text())
    require(inventory["commit"] == "139105d28c7685a154cb3093f79edb2e16708099",
            "library version")
    require(inventory["lean_toolchain"] == "leanprover/lean4:v4.36.0-rc2",
            "toolchain version")
    local_links = 0
    for path in BASE.glob("*.md"):
        content = path.read_text()
        require(content.count(r"\(") == content.count(r"\)"), ("inline math", path))
        require(content.count(r"\[") == content.count(r"\]"), ("display math", path))
        for raw in re.findall(r"\]\((<[^>]+>|[^)\s]+)\)", content):
            href = raw.strip("<>")
            if href.startswith(("http://", "https://", "#")):
                continue
            stem = re.sub(r":\d+$", "", href)
            target = Path(stem) if stem.startswith("/") else path.parent / stem
            require(target.exists(), ("missing local link", path.name, href))
            local_links += 1
    require((BASE / "P14_LEAN_OVERVIEW.png").stat().st_size > 1000, "PNG absent")
    require((BASE / "P14_LEAN_OVERVIEW.svg").stat().st_size > 1000, "SVG absent")
    require(not list(ROOT.rglob("*.lean")), "unexpected Lean implementation")
    report = {
        "status": "PASS_PLAN_COVERAGE_AND_ACCOUNTING",
        "paper_ids": len(ids), "modules": len(modules), "published_inputs": len(published),
        "quotient_edges": len(quotient), "combined_interface_edges": len(edges),
        "acyclic": True, "mapping_duplicates": [], "unassigned_ids": [],
        "module_effort_person_days": [low, high],
        "including_setup_person_days": [low + 2, high + 5],
        "public_main_module_rows_checked": 18,
        "preserved_V03_members": len(preserve),
        "public_document_local_links_checked": local_links,
        "diagram_files_present": True,
        "Lean_compilation": "NOT_ATTEMPTED",
        "scope": "Plan declarations, coverage, arithmetic, source identity and document links. No validation of effort forecasts or formal proof truth.",
    }
    (BASE / "audits/PLAN_CHECK.json").write_text(json.dumps(report, ensure_ascii=False, indent=2) + "\n")
    print(json.dumps(report, ensure_ascii=False, indent=2))


if __name__ == "__main__":
    main()
