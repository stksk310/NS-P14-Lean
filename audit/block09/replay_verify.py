#!/usr/bin/env python3
"""Replay submitted verifier, writing fresh output under audit/block09/replay.

Only repository/output path resolution differs from scripts/verify_block09.py.
"""
from pathlib import Path
import hashlib
import json
import re
import subprocess
import time

root = Path(__file__).resolve().parents[2]
out = root / 'audit/block09/replay'
out.mkdir(parents=True, exist_ok=True)
sources = ['NSP14/Semigroup/' + name + '.lean' for name in [
    'Ring', 'IdealPowers', 'RingCoordinates', 'GradedPieces',
    'GradedProduct', 'GradedBasis', 'TangentAction']]
previous = [
    ('block01_regression', 'tests/SmallScalar.lean', 10),
    ('block02_regression', 'tests/Sidon.lean', 14),
    ('block03_regression', 'tests/Resources.lean', 7),
    ('block04_regression', 'tests/LowRank.lean', 13),
    ('block05_regression', 'tests/LargeSeed.lean', 22),
    ('block06_regression', 'tests/LargeScalar.lean', 15),
    ('block07_regression', 'tests/OrdinaryNumerical.lean', 25),
    ('block08_regression', 'tests/SemigroupFoundations.lean', 86),
]
commands = [('build', ['lake', 'build'])]
commands += [(Path(path).stem.lower() + '_recheck', ['lake', 'env', 'lean', path])
             for path in sources]
commands += [('tests_and_axioms', ['lake', 'env', 'lean', 'tests/SemigroupRing.lean'])]
commands += [(name, ['lake', 'env', 'lean', path]) for name, path, _ in previous]
commands += [
    ('block01_domain_checks', ['lake', 'env', 'lean', 'audit/DomainChecks.lean']),
    ('block02_assumption_checks', ['lake', 'env', 'lean', 'audit/block02/AssumptionChecks.lean'])]
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
    if re.search(r'\bwarning:', result.stdout):
        raise RuntimeError(('Warnings in verification output', name))

allowed = {'propext', 'Classical.choice', 'Quot.sound'}
declarations = []
for path in sources:
    for kind, name in re.findall(r'^(?:noncomputable )?(def|abbrev|theorem|instance) (\w+)',
                                 (root / path).read_text(), re.M):
        declarations.append({'kind': kind, 'name': 'NSP14.NumericalSemigroup.' + name})
expected = {item['name'] for item in declarations}
counts = {}
for name, count in [('tests_and_axioms', len(expected))] + [(a, c) for a, _, c in previous]:
    output = (out / (name + '.log')).read_text()
    reports = re.findall(r"'([^']+)' (?:depends on axioms:\s*\[([^]]*)\]|does not depend on any axioms)",
                         output, re.S)
    if len(reports) != count:
        raise RuntimeError(('Unexpected axiom report count', name, len(reports), count))
    if name == 'tests_and_axioms' and {decl for decl, _ in reports} != expected:
        raise RuntimeError('Block09 axiom reports do not match all named public declarations')
    for decl, group in reports:
        actual = {v.strip() for v in group.split(',') if v.strip()}
        if not actual <= allowed:
            raise RuntimeError(('Unexpected axiom', decl, actual - allowed))
    counts[name] = len(reports)

baseline = json.loads((root / 'verification/block08/MANIFEST_SHA256.json').read_text())
paths = ['lean-toolchain', 'lakefile.toml', 'lake-manifest.json']
paths += sorted(path for path in baseline if path.startswith('NSP14/') and path.endswith('.lean'))
paths += [path for _, path, _ in previous]
for path in paths:
    actual = hashlib.sha256((root / path).read_bytes()).hexdigest()
    if actual != baseline[path]:
        raise RuntimeError(('Predecessor or fixed environment changed', path))

record = {
    'status': 'PASS_COMPILED_BLOCK09', 'date_jst': '2026-11-10',
    'checks': records, 'axiom_report_counts': counts,
    'block09_declarations': declarations,
    'block09_theorem_count': sum(d['kind'] == 'theorem' for d in declarations),
    'allowed_axioms': sorted(allowed), 'new_mathematical_axioms': [],
    'predecessor_sources_tests_and_fixed_environment_match_block08': True,
    'predecessor_hash_count': len(paths), 'sources': sources,
    'paper_source': 'V02 section2; V03 O_COORD, algebraic semigroup-ring coordinate step',
    'scope': 'Actual positive ideal powers equal numerical-order monomial ideals. Exact-order coordinates give finite bases of homogeneous quotients; quotient multiplication and terminal monomial/kernel criterion are constructed.',
    'paper_alignment_ledger': 'docs/LEAN_PAPER_ALIGNMENT_JA.md, A12-A14',
    'remaining': ['completion and algebraic/completed associated-graded comparison',
                  'assembly as one graded algebra with associativity/unit laws',
                  'full kernel and head/cokernel bases; A/N/Q and same-jump modules',
                  'actual offset-volume/cut/tower resources; maximal Q2 to pair data',
                  'Koszul/Tor, target Betti input and full P14'],
}
(out / 'verification.json').write_text(json.dumps(record, indent=2) + '\n')
print('PASS', len(commands), 'commands;', sum(counts.values()), 'axiom reports;', len(paths), 'baseline hashes')
