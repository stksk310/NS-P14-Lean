#!/usr/bin/env python3
"""Recheck resource-derived SO3, both predecessor blocks, and axiom dependencies."""
from pathlib import Path
import hashlib
import json
import re
import subprocess
import time

root = Path(__file__).resolve().parents[1]
out = root / 'verification/block03'
out.mkdir(parents=True, exist_ok=True)
commands = [
    ('build', ['lake', 'build']),
    ('source_recheck', ['lake', 'env', 'lean', 'NSP14/Ordinary/Resources.lean']),
    ('tests_and_axioms', ['lake', 'env', 'lean', 'tests/Resources.lean']),
    ('block01_regression', ['lake', 'env', 'lean', 'tests/SmallScalar.lean']),
    ('block02_regression', ['lake', 'env', 'lean', 'tests/Sidon.lean']),
    ('block01_domain_checks', ['lake', 'env', 'lean', 'audit/DomainChecks.lean']),
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
prefix = 'NSP14.Ordinary.SmallScalar.'
expected = {
    prefix + name for name in [
        'residual_weight_nonneg', 'residual_weight_nonpos', 'residual_tail_le',
        'Resources.scalar_le_upper', 'Resources.scalar_lt',
        'Resources.scalar_lt_of_boundary_sidon', 'Resources.scalar_lt_of_apery_pairs',
    ]
}
counts = {}
for name, count in [('tests_and_axioms', 7), ('block01_regression', 10),
                    ('block02_regression', 14)]:
    text = (out / (name + '.log')).read_text()
    reports = re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]", text, re.S)
    if len(reports) != count:
        raise RuntimeError(('Unexpected axiom report count', name, len(reports)))
    if name == 'tests_and_axioms' and {theorem for theorem, _ in reports} != expected:
        raise RuntimeError('Block03 axiom report names do not match the public theorems')
    for theorem, group in reports:
        actual = {v.strip() for v in group.split(',') if v.strip()}
        if not actual <= allowed:
            raise RuntimeError(('Unexpected axiom', theorem, actual - allowed))
    counts[name] = len(reports)

# Keep the reviewed predecessor sources and fixed environment unchanged.
baselines = {
    'verification/block01/MANIFEST_SHA256.json': [
        'lean-toolchain', 'lakefile.toml', 'lake-manifest.json',
        'NSP14/Ordinary/SmallScalar.lean', 'tests/SmallScalar.lean',
    ],
    'verification/block02/MANIFEST_SHA256.json': [
        'NSP14/Combinatorics/Sidon.lean', 'tests/Sidon.lean',
    ],
}
for manifest, paths in baselines.items():
    entries = json.loads((root / manifest).read_text())
    for path in paths:
        actual = hashlib.sha256((root / path).read_bytes()).hexdigest()
        if actual != entries[path]:
            raise RuntimeError(('Reviewed predecessor or fixed environment changed', path))

record = {
    'status': 'PASS_COMPILED_BLOCK03',
    'checks': records,
    'axiom_report_counts': counts,
    'block03_theorems': sorted(expected),
    'allowed_axioms': sorted(allowed),
    'new_mathematical_axioms': [],
    'predecessor_sources_and_fixed_environment_match_baselines': True,
    'source': 'NSP14/Ordinary/Resources.lean',
    'paper_source': 'auditability_search/ORDINARY_PAPER_REDUCTION_JA.md, section 2 SO3 and section 3 SO5',
    'scope': 'SO3 for arbitrary finite resource supports, r >= 4, n >= r; SO5 at ranks 4..8 composed with Block01 and boundary Sidon or numeric Apery data.',
    'remaining': ['actual tangent-cone construction of the common resource profile',
                  'maximal actual Q2 implies numerical Apery-pair data',
                  'ranks 2,3 and >=9 scalar closure', 'Tor/Betti semantics and full P14'],
}
(out / 'verification.json').write_text(json.dumps(record, indent=2) + '\n')
print(json.dumps(record, indent=2))
