#!/usr/bin/env python3
"""Recheck all numerical low-rank rows and regressions of Blocks 01–03."""
from pathlib import Path
import hashlib
import json
import re
import subprocess
import time

root = Path(__file__).resolve().parents[1]
out = root / 'verification/block04'
out.mkdir(parents=True, exist_ok=True)
commands = [
    ('build', ['lake', 'build']),
    ('source_recheck', ['lake', 'env', 'lean', 'NSP14/Ordinary/LowRank.lean']),
    ('tests_and_axioms', ['lake', 'env', 'lean', 'tests/LowRank.lean']),
    ('block01_regression', ['lake', 'env', 'lean', 'tests/SmallScalar.lean']),
    ('block02_regression', ['lake', 'env', 'lean', 'tests/Sidon.lean']),
    ('block03_regression', ['lake', 'env', 'lean', 'tests/Resources.lean']),
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
    'NSP14.Ordinary.LowRank.' + name for name in [
        'Layers.tail_sum_nonneg', 'Layers.row_le', 'Layers.rank_two_first_le_mass',
        'Layers.rank_two_first_le_linear', 'Layers.rank_two_top_le', 'Layers.rank_two_bounds',
        'Layers.rank_three_first_le', 'Layers.rank_three_second_le', 'Layers.rank_three_top_le',
        'rank_three_margin_pos', 'Layers.rank_three_bounds',
    ]
} | {'NSP14.Ordinary.SmallScalar.Resources.' + name for name in
     ['row_one_eq_scalar', 'rank_three_bounds']}
counts = {}
for name, count in [('tests_and_axioms', 13), ('block01_regression', 10),
                    ('block02_regression', 14), ('block03_regression', 7)]:
    text = (out / (name + '.log')).read_text()
    reports = re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]", text, re.S)
    if len(reports) != count:
        raise RuntimeError(('Unexpected axiom report count', name, len(reports)))
    if name == 'tests_and_axioms' and {theorem for theorem, _ in reports} != expected:
        raise RuntimeError('Block04 axiom report names do not match the public theorems')
    for theorem, group in reports:
        actual = {v.strip() for v in group.split(',') if v.strip()}
        if not actual <= allowed:
            raise RuntimeError(('Unexpected axiom', theorem, actual - allowed))
    counts[name] = len(reports)

baseline = json.loads((root / 'verification/block03/MANIFEST_SHA256.json').read_text())
paths = ['lean-toolchain', 'lakefile.toml', 'lake-manifest.json',
         'NSP14/Ordinary/SmallScalar.lean', 'NSP14/Combinatorics/Sidon.lean',
         'NSP14/Ordinary/Resources.lean', 'tests/SmallScalar.lean',
         'tests/Sidon.lean', 'tests/Resources.lean']
for path in paths:
    actual = hashlib.sha256((root / path).read_bytes()).hexdigest()
    if actual != baseline[path]:
        raise RuntimeError(('Predecessor or fixed environment changed', path))

record = {
    'status': 'PASS_COMPILED_BLOCK04', 'date_jst': '2026-11-10',
    'checks': records, 'axiom_report_counts': counts,
    'block04_theorems': sorted(expected), 'allowed_axioms': sorted(allowed),
    'new_mathematical_axioms': [],
    'predecessor_sources_tests_and_fixed_environment_match_block03': True,
    'source': 'NSP14/Ordinary/LowRank.lean',
    'paper_source': 'proof_integrated_v2/NS_P14_INTEGRATED_PROOF_JA.md, sections 7 and 9; V03 III.1 O_LOW',
    'scope': 'All rank-two and rank-three finite weighted numerical rows; zero deficit in rank two; adapter from Block03 resources with explicit linear head cap.',
    'remaining': ['actual common tower and its linear head cap',
                  'Koszul/Tor derivation of row upper bounds (7.3)',
                  'actual target margin (8.4) and Betti transfer',
                  'rank >=9 scalar closure', 'full M12 and full P14'],
}
(out / 'verification.json').write_text(json.dumps(record, indent=2) + '\n')
print(json.dumps(record, indent=2))
