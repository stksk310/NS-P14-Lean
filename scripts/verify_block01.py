#!/usr/bin/env python3
"""Build and inspect Block 01. Requires the pinned Lean/Lake on PATH."""
from pathlib import Path
import json
import re
import subprocess
import time

root = Path(__file__).resolve().parents[1]
out = root / 'verification/block01'
out.mkdir(parents=True, exist_ok=True)
commands = [
    ('build', ['lake', 'build']),
    ('source_recheck', ['lake', 'env', 'lean', 'NSP14/Ordinary/SmallScalar.lean']),
    ('tests_and_axioms', ['lake', 'env', 'lean', 'tests/SmallScalar.lean']),
    ('domain_checks', ['lake', 'env', 'lean', 'audit/DomainChecks.lean']),
]
records = []
for name, cmd in commands:
    started = time.monotonic()
    result = subprocess.run(cmd, cwd=root, text=True, stdout=subprocess.PIPE,
                            stderr=subprocess.STDOUT)
    (out / (name + '.log')).write_text(result.stdout)
    print(name, 'exit', result.returncode, flush=True)
    records.append({'command': cmd, 'exit_code': result.returncode,
                    'seconds': round(time.monotonic() - started, 3)})
    if result.returncode:
        print(result.stdout)
        raise SystemExit(result.returncode)
text = (out / 'tests_and_axioms.log').read_text()
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
sets = re.findall(r'depends on axioms:\s*\[([^]]*)\]', text, flags=re.S)
if len(sets) != 10:
    raise RuntimeError(('Expected ten axiom reports', text))
for group in sets:
    actual = {v.strip() for v in group.split(',') if v.strip()}
    if not actual <= allowed:
        raise RuntimeError(('Unexpected axiom', actual - allowed))
record_path = out / 'verification.json'
record = json.loads(record_path.read_text()) if record_path.exists() else {}
record.update({'status': 'PASS_COMPILED_BLOCK01', 'checks': records,
          'axiom_reports': len(sets), 'allowed_axioms': sorted(allowed),
          'new_mathematical_axioms': [], 'scope':
          'Five-row rational scalar block only; corner feasibility and SO3 resource bound remain explicit premises.',
          'shift_domains': {'gap_shift': 'arbitrary s,t : Q',
                           'small_gap_pos': 's,t : N; 4 <= r <= 8; r <= 5 or s+t != 0'},
          'negative_integer_shift_counterexample_checked': True})
(out / 'verification.json').write_text(json.dumps(record, indent=2) + '\n')
print(json.dumps(record, indent=2))
