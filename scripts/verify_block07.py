#!/usr/bin/env python3
"""Recheck integrated ordinary numerical closure and Blocks 01–06."""
from pathlib import Path
import hashlib
import json
import re
import subprocess
import time

root = Path(__file__).resolve().parents[1]
out = root / 'verification/block07'
out.mkdir(parents=True, exist_ok=True)
commands = [
    ('build', ['lake', 'build']),
    ('scalarization_recheck', ['lake', 'env', 'lean', 'NSP14/Ordinary/Scalarization.lean']),
    ('target_margin_recheck', ['lake', 'env', 'lean', 'NSP14/Ordinary/TargetMargin.lean']),
    ('closure_recheck', ['lake', 'env', 'lean', 'NSP14/Ordinary/NumericalClosure.lean']),
    ('tests_and_axioms', ['lake', 'env', 'lean', 'tests/OrdinaryNumerical.lean']),
    ('block01_regression', ['lake', 'env', 'lean', 'tests/SmallScalar.lean']),
    ('block02_regression', ['lake', 'env', 'lean', 'tests/Sidon.lean']),
    ('block03_regression', ['lake', 'env', 'lean', 'tests/Resources.lean']),
    ('block04_regression', ['lake', 'env', 'lean', 'tests/LowRank.lean']),
    ('block05_regression', ['lake', 'env', 'lean', 'tests/LargeSeed.lean']),
    ('block06_regression', ['lake', 'env', 'lean', 'tests/LargeScalar.lean']),
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
groups = {
    'Scalarization': [
        'choose_balance', 'binomial_balance', 'factor_nonneg', 'factor_pos',
        'head_weight_eq', 'tail_weight_eq', 'second_tail_identity', 'normalized_tail_le',
        'weight_zero_le', 'weight_head_le', 'weight_tail_le', 'row_le_scalar',
    ],
    'TargetMargin': [
        'choose_succ_cast', 'target_zero', 'target_step', 'capacity_step', 'target_margin',
    ],
    'NumericalClosure.Data': [
        'deficit_nat_lower', 'parameterization', 'small_corner', 'scalar_lt',
        'row_capacity', 'all_rows', 'all_rows_of_apery_pairs', 'relative_rows',
    ],
}
expected = {'NSP14.Ordinary.' + namespace + '.' + name
            for namespace, names in groups.items() for name in names}
counts = {}
for name, count in [('tests_and_axioms', 25), ('block01_regression', 10),
                    ('block02_regression', 14), ('block03_regression', 7), ('block04_regression', 13),
                    ('block05_regression', 22), ('block06_regression', 15)]:
    text = (out / (name + '.log')).read_text()
    reports = re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]", text, re.S)
    if len(reports) != count:
        raise RuntimeError(('Unexpected axiom report count', name, len(reports)))
    if name == 'tests_and_axioms' and {theorem for theorem, _ in reports} != expected:
        raise RuntimeError('Block07 axiom report names do not match the public theorems')
    for theorem, group in reports:
        actual = {v.strip() for v in group.split(',') if v.strip()}
        if not actual <= allowed:
            raise RuntimeError(('Unexpected axiom', theorem, actual - allowed))
    counts[name] = len(reports)

baseline = json.loads((root / 'verification/block06/MANIFEST_SHA256.json').read_text())
paths = ['lean-toolchain', 'lakefile.toml', 'lake-manifest.json',
         'NSP14/Ordinary/SmallScalar.lean', 'NSP14/Combinatorics/Sidon.lean',
         'NSP14/Ordinary/Resources.lean', 'NSP14/Ordinary/LowRank.lean',
         'NSP14/Ordinary/LargeSeed.lean', 'NSP14/Ordinary/LargeScalar.lean', 'tests/SmallScalar.lean',
         'tests/Sidon.lean', 'tests/Resources.lean', 'tests/LowRank.lean', 'tests/LargeSeed.lean', 'tests/LargeScalar.lean']
for path in paths:
    actual = hashlib.sha256((root / path).read_bytes()).hexdigest()
    if actual != baseline[path]:
        raise RuntimeError(('Predecessor or fixed environment changed', path))

record = {
    'status': 'PASS_COMPILED_BLOCK07', 'date_jst': '2026-11-10',
    'checks': records, 'axiom_report_counts': counts,
    'block07_theorems': sorted(expected), 'allowed_axioms': sorted(allowed),
    'new_mathematical_axioms': [],
    'predecessor_sources_tests_and_fixed_environment_match_block06': True,
    'sources': ['NSP14/Ordinary/Scalarization.lean', 'NSP14/Ordinary/TargetMargin.lean',
                'NSP14/Ordinary/NumericalClosure.lean'],
    'paper_source': 'proof_integrated_v2/NS_P14_INTEGRATED_PROOF_JA.md, sections 7.3,8.2-8.4,9-11; V03 ordinary numerical chain',
    'scope': 'Common finite resource data plus explicit small-boundary Sidon or numerical Apery data imply L_k+weighted_row<=R_k for all 1<=k<=r and every cut rank r>=2. No actual tower/Tor/Betti construction.',
    'paper_alignment_ledger': 'docs/LEAN_PAPER_ALIGNMENT_JA.md, A07-A09',
    'remaining': ['actual common tower and simultaneous resource caps',
                  'maximal actual Q2 to Apery data',
                  'actual Koszul/Tor row bounds and ordinary target Betti formula',
                  'actual Betti transfer, other branches, and full P14'],
}
(out / 'verification.json').write_text(json.dumps(record, indent=2) + '\n')
print(json.dumps(record, indent=2))
