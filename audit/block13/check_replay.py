#!/usr/bin/env python3
"""Compare replay declarations with the pinned submission, independently of closure flags."""
from pathlib import Path
import json
import re

root = Path(__file__).resolve().parents[2]
out = root/'audit/block13'
submitted = root/'verification/block13_continuation'
replay = out/'replay'
a, b = (json.loads((p/'verification.json').read_text()) for p in (submitted, replay))
assert b['status'] == 'PASS_FORMAL_VERIFICATION'
assert len(b['checks']) == 40
assert all(x['exit_code'] == 0 for x in b['checks'])
assert len(b['sources']) == 69 and len(b['acceptance_tests']) == 17
assert b['core_line_count'] == 5895
assert b['core_declarations'] == 1207 and b['test_declarations'] == 77
assert b['frozen_hash_count'] == 84
assert sum(b['old_axiom_reports'].values()) == 741
for k in ['sources', 'acceptance_tests', 'old_axiom_reports', 'allowed_axioms']:
    assert a[k] == b[k], k

def declarations(folder):
    rows = json.loads((folder/'declarations.json').read_text())
    assert len(rows) == 1284
    assert len({x['name'] for x in rows}) == len(rows)
    for d in rows:
        assert set(d['axioms']) <= {'propext', 'Classical.choice', 'Quot.sound'}
        assert d['name'] not in d['axioms']
    return {d['name']: {k: d[k] for k in ['module', 'exported_kind', 'type', 'explicit_type', 'axioms']}
            for d in rows}

assert declarations(submitted) == declarations(replay)
for name in b['sources']+b['acceptance_tests']:
    text = (root/name).read_text()
    assert not re.search(r'\b(?:sorry|admit|sorryAx|native_decide|unsafe|implemented_by|extern)\b', text), name
    assert not re.search(r'^\s*(?:private\s+|protected\s+)?axiom\s', text, re.M), name
for log in replay.glob('*.log'):
    assert not re.search(r'\bwarning:', log.read_text()), log
boundary = (out/'boundary_checks.log').read_text()
assert 'error:' not in boundary and 'warning:' not in boundary
reports = re.findall(r"'([^']+)' (?:depends on axioms:\s*\[([^]]*)\]|does not depend on any axioms)",
                     boundary, re.S)
assert len(reports) == 4
for name, axs in reports:
    assert {x.strip() for x in axs.split(',') if x.strip()} <= {'propext', 'Classical.choice', 'Quot.sound'}
result = dict(status='PASS', replay_checks=40, new_environment_declarations=1284,
              declaration_names_types_and_axioms_match_submission=True,
              predecessor_axiom_reports=741, independent_boundary_axiom_reports=4,
              forbidden_source_constructs_found=False, warnings_found=False,
              closure_flags_are_not_mathematical_evidence=True)
(out/'replay_comparison.json').write_text(json.dumps(result, indent=2)+'\n')
print(json.dumps(result, indent=2))
