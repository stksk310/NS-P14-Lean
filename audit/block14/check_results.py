#!/usr/bin/env python3
"""Final evidence gates for the independent Run14 audit."""
from pathlib import Path
import gzip
import json
import re
import subprocess

root = Path(__file__).resolve().parents[2]
out = root/'audit/block14'
fixed = root/'verification/run14_reproducibility_fix'
v = json.loads((fixed/'verification.json').read_text())
assert v['status'] == 'PASS_RUN14_CLOSURE' and v['fresh_project_test_cache']
assert len(v['checks']) == 50 and all(c['exit_code'] == 0 for c in v['checks'])
assert v['environment_declarations'] == 3217 and v['new_environment_declarations'] == 544
for x in v['checks']:
    suffix = '.log.gz' if x['name'] == 'environment_axioms' else '.log'
    p = fixed/(x['name']+suffix)
    s = gzip.decompress(p.read_bytes()).decode() if suffix.endswith('.gz') else p.read_text()
    assert 'warning:' not in s, p
for name in ['declarations.json.gz', 'environment_axioms.log.gz']:
    submitted = subprocess.check_output(['git', 'show',
        f'fbfa5de:verification/run14_continuation/{name}'], cwd=root)
    assert gzip.decompress((fixed/name).read_bytes()) == gzip.decompress(submitted), name
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
declarations = json.loads(gzip.decompress((fixed/'declarations.json.gz').read_bytes()))
assert len({d['name'] for d in declarations}) == 3217
for d in declarations:
    assert set(d['axioms']) <= allowed and d['name'] not in d['axioms'], d['name']
core = json.loads(gzip.decompress((out/'core_types.json.gz').read_bytes()))
assert len(core) == 699 and len({x['module'] for x in core}) == 49
boundary = (out/'boundary_checks.log').read_text()
assert 'warning:' not in boundary and 'error:' not in boundary and 'sorryAx' not in boundary
reports = re.findall(r"'([^']+)' (?:depends on axioms:\s*\[([^]]*)\]|does not depend on any axioms)", boundary, re.S)
assert len(reports) == 8
for _, axs in reports:
    assert {a.strip() for a in axs.split(',') if a.strip()} <= allowed
sources = subprocess.check_output(['git', 'diff', '--name-only', 'd8556dc', 'fbfa5de', '--', 'NSP14'], cwd=root, text=True).splitlines()
for p in sources:
    s = (root/p).read_text()
    assert not re.search(r'\b(?:sorry|admit|sorryAx|unsafe|native_decide|implemented_by|extern)\b', s), p
    assert not re.search(r'^\s*(?:(?:public|private|protected)\s+)?axiom\b', s, re.M), p
for name in ['integrity.json', 'core_type_check.json', 'finite_models.json']:
    assert json.loads((out/name).read_text())['status'] == 'PASS', name
result = dict(status='PASS', repaired_replay_commands=50, environment_declarations=3217,
              current_Run14_core_types=699, core_modules=49, independent_boundary_reports=8,
              allowed_axioms=sorted(allowed), warning_count=0,
              additional_mathematical_axioms=[], source_guard='PASS')
(out/'evidence_check.json').write_text(json.dumps(result, indent=2)+'\n')
print(json.dumps(result, indent=2))
