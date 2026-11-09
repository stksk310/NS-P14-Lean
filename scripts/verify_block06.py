#!/usr/bin/env python3
"""Recheck universal rational large-rank scalar closure and Blocks 01–05."""
from pathlib import Path
import hashlib
import json
import re
import subprocess
import time

root = Path(__file__).resolve().parents[1]
out = root / 'verification/block06'
out.mkdir(parents=True, exist_ok=True)
commands = [
    ('build', ['lake', 'build']),
    ('source_recheck', ['lake', 'env', 'lean', 'NSP14/Ordinary/LargeScalar.lean']),
    ('tests_and_axioms', ['lake', 'env', 'lean', 'tests/LargeScalar.lean']),
    ('block01_regression', ['lake', 'env', 'lean', 'tests/SmallScalar.lean']),
    ('block02_regression', ['lake', 'env', 'lean', 'tests/Sidon.lean']),
    ('block03_regression', ['lake', 'env', 'lean', 'tests/Resources.lean']),
    ('block04_regression', ['lake', 'env', 'lean', 'tests/LowRank.lean']),
    ('block05_regression', ['lake', 'env', 'lean', 'tests/LargeSeed.lean']),
    ('block01_domain_checks', ['lake', 'env', 'lean', 'audit/DomainChecks.lean']),
    ('block02_assumption_checks', ['lake', 'env', 'lean', 'audit/block02/AssumptionChecks.lean']),
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
expected = {
    'NSP14.Ordinary.LargeScalar.' + name for name in [
        'triangular_large', 'alpha_bounds', 'seed_slope_identity', 'step_identity',
        'correction_neg', 'baseSlope_lower', 'baseSlope_pos', 'floor_comparison_identity',
        'floorStep_le_stepLower', 'floorStep_gt', 'baseStep_gt', 'quadrant_identity',
        'gap_pos_shift', 'large_gap_pos',
    ]
} | {'NSP14.Ordinary.SmallScalar.Resources.scalar_lt_large'}
counts = {}
for name, count in [('tests_and_axioms', 15), ('block01_regression', 10),
                    ('block02_regression', 14), ('block03_regression', 7), ('block04_regression', 13),
                    ('block05_regression', 22)]:
    text = (out / (name + '.log')).read_text()
    reports = re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]", text, re.S)
    if len(reports) != count:
        raise RuntimeError(('Unexpected axiom report count', name, len(reports)))
    if name == 'tests_and_axioms' and {theorem for theorem, _ in reports} != expected:
        raise RuntimeError('Block06 axiom report names do not match the public theorems')
    for theorem, group in reports:
        actual = {v.strip() for v in group.split(',') if v.strip()}
        if not actual <= allowed:
            raise RuntimeError(('Unexpected axiom', theorem, actual - allowed))
    counts[name] = len(reports)

baseline = json.loads((root / 'verification/block05/MANIFEST_SHA256.json').read_text())
paths = ['lean-toolchain', 'lakefile.toml', 'lake-manifest.json',
         'NSP14/Ordinary/SmallScalar.lean', 'NSP14/Combinatorics/Sidon.lean',
         'NSP14/Ordinary/Resources.lean', 'NSP14/Ordinary/LowRank.lean',
         'NSP14/Ordinary/LargeSeed.lean', 'tests/SmallScalar.lean',
         'tests/Sidon.lean', 'tests/Resources.lean', 'tests/LowRank.lean', 'tests/LargeSeed.lean']
for path in paths:
    actual = hashlib.sha256((root / path).read_bytes()).hexdigest()
    if actual != baseline[path]:
        raise RuntimeError(('Predecessor or fixed environment changed', path))

record = {
    'status': 'PASS_COMPILED_BLOCK06', 'date_jst': '2026-11-10',
    'checks': records, 'axiom_report_counts': counts,
    'block06_theorems': sorted(expected), 'allowed_axioms': sorted(allowed),
    'new_mathematical_axioms': [],
    'predecessor_sources_tests_and_fixed_environment_match_block05': True,
    'source': 'NSP14/Ordinary/LargeScalar.lean',
    'paper_source': 'proof_integrated_v2/NS_P14_INTEGRATED_PROOF_JA.md, section 11 S21-S31; V03 III.5 O_LARGE O22-O23',
    'scope': 'Large-rank gap positivity and resource-derived scalar bound for every r>=9 and rational e>=10,d>=a_r. No actual Tor/Betti construction.',
    'paper_alignment_ledger': 'docs/LEAN_PAPER_ALIGNMENT_JA.md, A06',
    'remaining': ['general all-row scalarization for ranks >=4',
                  'actual common tower and its resource caps',
                  'Koszul/Tor, target margins and Betti transfer', 'full M12 and full P14'],
}
(out / 'verification.json').write_text(json.dumps(record, indent=2) + '\n')
print(json.dumps(record, indent=2))
