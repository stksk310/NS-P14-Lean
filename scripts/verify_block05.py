#!/usr/bin/env python3
"""Recheck the universal large-rank seed and regressions of Blocks 01–04."""
from pathlib import Path
import hashlib
import json
import re
import subprocess
import time

root = Path(__file__).resolve().parents[1]
out = root / 'verification/block05'
out.mkdir(parents=True, exist_ok=True)
commands = [
    ('build', ['lake', 'build']),
    ('source_recheck', ['lake', 'env', 'lean', 'NSP14/Ordinary/LargeSeed.lean']),
    ('tests_and_axioms', ['lake', 'env', 'lean', 'tests/LargeSeed.lean']),
    ('block01_regression', ['lake', 'env', 'lean', 'tests/SmallScalar.lean']),
    ('block02_regression', ['lake', 'env', 'lean', 'tests/Sidon.lean']),
    ('block03_regression', ['lake', 'env', 'lean', 'tests/Resources.lean']),
    ('block04_regression', ['lake', 'env', 'lean', 'tests/LowRank.lean']),
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
    "NSP14.Ordinary.LargeSeed." + name for name in [
        'triangularNat_cast', 'triangularNat_succ', 'triangular_nonneg',
        'cutoff_bounds', 'cutoff_admissible', 'cutoff_step',
        'harmonic_add', 'harmonic_add_le', 'harmonic_cutoff_step',
        'barrier_step_identity', 'barrier_step_gt', 'harmonic_base',
        'harmonic_lt_barrier', 'threshold_gap_identity', 'barrier_lt_thresholdLower',
        'thresholdLower_le_threshold', 'harmonic_lt_threshold', 'harmonic_tail',
        'tailWeight_eq', 'seed_eq_threshold', 'rank_nine_seed', 'large_seed_pos',
    ]
}
counts = {}
for name, count in [('tests_and_axioms', 22), ('block01_regression', 10),
                    ('block02_regression', 14), ('block03_regression', 7), ('block04_regression', 13)]:
    text = (out / (name + '.log')).read_text()
    reports = re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]", text, re.S)
    if len(reports) != count:
        raise RuntimeError(('Unexpected axiom report count', name, len(reports)))
    if name == 'tests_and_axioms' and {theorem for theorem, _ in reports} != expected:
        raise RuntimeError('Block05 axiom report names do not match the public theorems')
    for theorem, group in reports:
        actual = {v.strip() for v in group.split(',') if v.strip()}
        if not actual <= allowed:
            raise RuntimeError(('Unexpected axiom', theorem, actual - allowed))
    counts[name] = len(reports)

baseline = json.loads((root / 'verification/block04/MANIFEST_SHA256.json').read_text())
paths = ['lean-toolchain', 'lakefile.toml', 'lake-manifest.json',
         'NSP14/Ordinary/SmallScalar.lean', 'NSP14/Combinatorics/Sidon.lean',
         'NSP14/Ordinary/Resources.lean', 'NSP14/Ordinary/LowRank.lean', 'tests/SmallScalar.lean',
         'tests/Sidon.lean', 'tests/Resources.lean', 'tests/LowRank.lean']
for path in paths:
    actual = hashlib.sha256((root / path).read_bytes()).hexdigest()
    if actual != baseline[path]:
        raise RuntimeError(('Predecessor or fixed environment changed', path))

record = {
    'status': 'PASS_COMPILED_BLOCK05', 'date_jst': '2026-11-10',
    'checks': records, 'axiom_report_counts': counts,
    'block05_theorems': sorted(expected), 'allowed_axioms': sorted(allowed),
    'new_mathematical_axioms': [],
    'predecessor_sources_tests_and_fixed_environment_match_block04': True,
    'source': 'NSP14/Ordinary/LargeSeed.lean',
    'paper_source': 'proof_integrated_v2/NS_P14_INTEGRATED_PROOF_JA.md, section 11 S2,S6-S20; V03 III.5 O_LARGE O21',
    'scope': 'Universal harmonic barrier for r>=10 and positive base gap G_r(10,a_r) for every r>=9. No arbitrary-deficit closure yet.',
    'paper_alignment_ledger': 'docs/LEAN_PAPER_ALIGNMENT_JA.md, A05',
    'remaining': ['positive e/d finite differences and arbitrary-deficit large-rank closure',
                  'actual common tower and its resource caps',
                  'Koszul/Tor, target margins and Betti transfer', 'full M12 and full P14'],
}
(out / 'verification.json').write_text(json.dumps(record, indent=2) + '\n')
print(json.dumps(record, indent=2))
