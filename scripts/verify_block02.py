#!/usr/bin/env python3
"""Recheck Block02, its public interfaces, and Block01 regression."""
from pathlib import Path
import hashlib
import json
import re
import subprocess
import time

root = Path(__file__).resolve().parents[1]
out = root / 'verification/block02'
out.mkdir(parents=True, exist_ok=True)
commands = [
    ('build', ['lake', 'build']),
    ('source_recheck', ['lake', 'env', 'lean', 'NSP14/Combinatorics/Sidon.lean']),
    ('tests_and_axioms', ['lake', 'env', 'lean', 'tests/Sidon.lean']),
    ('block01_regression', ['lake', 'env', 'lean', 'tests/SmallScalar.lean']),
]
records = []
for name, cmd in commands:
    started = time.monotonic()
    result = subprocess.run(cmd, cwd=root, text=True, stdout=subprocess.PIPE,
                            stderr=subprocess.STDOUT)
    (out / (name + '.log')).write_text(result.stdout)
    records.append({'command': cmd, 'exit_code': result.returncode,
                    'seconds': round(time.monotonic() - started, 3)})
    print(name, 'exit', result.returncode, flush=True)
    if result.returncode:
        print(result.stdout)
        raise SystemExit(result.returncode)
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
for name, count in [('tests_and_axioms', 14), ('block01_regression', 10)]:
    text = (out / (name + '.log')).read_text()
    reports = re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]", text, re.S)
    if len(reports) != count:
        raise RuntimeError(('Unexpected report count', name, len(reports)))
    for theorem, group in reports:
        actual = {v.strip() for v in group.split(',') if v.strip()}
        if not actual <= allowed:
            raise RuntimeError(('Unexpected axiom', theorem, actual - allowed))
old = json.loads((root / 'verification/block01/MANIFEST_SHA256.json').read_text())
p = 'NSP14/Ordinary/SmallScalar.lean'
if hashlib.sha256((root / p).read_bytes()).hexdigest() != old[p]:
    raise RuntimeError('Block01 proof source changed')
record = {'status': 'PASS_COMPILED_BLOCK02', 'checks': records,
          'block02_axiom_reports': 14, 'block01_regression_axiom_reports': 10,
          'allowed_axioms': sorted(allowed), 'new_mathematical_axioms': [],
          'block01_proof_source_unchanged': True,
          'scope': 'Finite Sidon counting, numerical Apéry-pair witness bridge, scalar integration. No construction from maximal algebraic Q2 yet.'}
(out / 'verification.json').write_text(json.dumps(record, indent=2) + '\n')
print(json.dumps(record, indent=2))
