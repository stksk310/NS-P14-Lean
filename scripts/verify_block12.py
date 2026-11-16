#!/usr/bin/env python3
"""Check Run12 actual S0/jump-strata/degree/completed comparison and Blocks 01–11."""
from pathlib import Path
import hashlib
import json
import re
import subprocess
import time

root = Path(__file__).resolve().parents[1]
out = root / 'verification/block12'
out.mkdir(parents=True, exist_ok=True)
sources = ['NSP14/Semigroup/CompletedComparison.lean', 'NSP14/Semigroup/CompletedPieces.lean', 'NSP14/Semigroup/CompletedTransport.lean', 'NSP14/Semigroup/CoordinateSupport.lean', 'NSP14/Semigroup/FormalFactorization.lean', 'NSP14/Semigroup/FormalInclusion.lean', 'NSP14/Semigroup/FormalOrder.lean', 'NSP14/Semigroup/FormalSemigroupRing.lean', 'NSP14/Semigroup/FormalTangentAlgebra.lean', 'NSP14/Semigroup/FormalTangentScalars.lean', 'NSP14/Semigroup/JumpAction.lean', 'NSP14/Semigroup/JumpBounds.lean', 'NSP14/Semigroup/JumpDegrees.lean', 'NSP14/Semigroup/JumpFiltration.lean', 'NSP14/Semigroup/JumpHomogeneity.lean', 'NSP14/Semigroup/JumpSlice.lean', 'NSP14/Semigroup/JumpStrata.lean', 'NSP14/Semigroup/LiveSplit.lean', 'NSP14/Semigroup/PolynomialAction.lean', 'NSP14/Semigroup/PolynomialGrading.lean', 'NSP14/Semigroup/PolynomialPresentation.lean', 'NSP14/Semigroup/TerminalCoordinates.lean']
new_tests = ['tests/Run12BasicExamples.lean', 'tests/Run12Fixtures.lean', 'tests/JumpBounds.lean', 'tests/PolynomialAction.lean', 'tests/JumpStrata.lean', 'tests/CompletedComparison.lean']
# Inventory checks run on the current tree, independently of the stored declaration list.
baseline_inventory = json.loads((root / 'verification/block11/MANIFEST_SHA256.json').read_text())
actual_sources = sorted(str(p.relative_to(root)) for p in (root / 'NSP14').rglob('*.lean')
                        if str(p.relative_to(root)) not in baseline_inventory)
if actual_sources != sources:
    raise RuntimeError(('Unregistered new source files', actual_sources, sources))
actual_tests = sorted(str(p.relative_to(root)) for p in (root / 'tests').glob('*.lean')
                      if str(p.relative_to(root)) not in baseline_inventory)
if actual_tests != sorted(new_tests + ['tests/Run12Axioms.lean']):
    raise RuntimeError(('Unregistered new acceptance files', actual_tests))

def collect_declarations(path):
    namespaces, result = [], []
    for line in (root / path).read_text().splitlines():
        match = re.match(r'^namespace (\S+)', line)
        if match:
            namespaces.append(match[1])
            continue
        match = re.match(r'^end(?: (\S+))?$', line)
        if match and namespaces and match[1] == namespaces[-1]:
            namespaces.pop()
            continue
        match = re.match(r'^(?:noncomputable )?(def|abbrev|theorem|instance) (\w+)', line)
        if match:
            result.append({'kind': match[1], 'name': '.'.join(namespaces + [match[2]]), 'source': path})
    return result

stored_inventory = json.loads((out / 'declarations.json').read_text())
current_inventory = {'core': [d for p in sources for d in collect_declarations(p)],
                     'test_fixtures': [d for p in new_tests for d in collect_declarations(p)]}
if stored_inventory != current_inventory:
    raise RuntimeError('Current declarations differ from the complete axiom-audit inventory')

previous = [
    ('block01_regression', 'tests/SmallScalar.lean', 10),
    ('block02_regression', 'tests/Sidon.lean', 14),
    ('block03_regression', 'tests/Resources.lean', 7),
    ('block04_regression', 'tests/LowRank.lean', 13),
    ('block05_regression', 'tests/LargeSeed.lean', 22),
    ('block06_regression', 'tests/LargeScalar.lean', 15),
    ('block07_regression', 'tests/OrdinaryNumerical.lean', 25),
    ('block08_regression', 'tests/SemigroupFoundations.lean', 86),
    ('block09_regression', 'tests/SemigroupRing.lean', 60),
    ('block10_regression', 'tests/TangentAlgebra.lean', 71),
    ('block11_regression', 'tests/AperyQuotient.lean', 120),
]
commands = [('build', ['lake', 'build'])]
commands += [(Path(path).stem.lower() + '_recheck', ['lake', 'env', 'lean', path])
             for path in sources]
for path in new_tests:
    target = root / '.lake/build/lib/lean' / Path(path).with_suffix('.olean')
    target.parent.mkdir(parents=True, exist_ok=True)
    commands.append((Path(path).stem.lower() + '_acceptance', ['lake', 'env', 'lean', path, '-o', str(target)]))
commands += [('tests_and_axioms', ['lake', 'env', 'lean', 'tests/Run12Axioms.lean'])]
commands += [('run_schedule', ['python3', 'lean_planning/checks/check_run_schedule_r02.py'])]
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
declaration_record = json.loads((out / 'declarations.json').read_text())
declarations = declaration_record['core']
test_declarations = declaration_record['test_fixtures']
expected = {item['name'] for item in declarations + test_declarations}
counts = {}
for name, count in [('tests_and_axioms', len(expected))] + [(a, c) for a, _, c in previous]:
    output = (out / (name + '.log')).read_text()
    reports = re.findall(r"'([^']+)' (?:depends on axioms:\s*\[([^]]*)\]|does not depend on any axioms)",
                         output, re.S)
    if len(reports) != count:
        raise RuntimeError(('Unexpected axiom report count', name, len(reports), count))
    if name == 'tests_and_axioms' and {decl for decl, _ in reports} != expected:
        raise RuntimeError('Run12 axiom reports do not match all named public declarations')
    for decl, group in reports:
        actual = {v.strip() for v in group.split(',') if v.strip()}
        if not actual <= allowed:
            raise RuntimeError(('Unexpected axiom', decl, actual - allowed))
    counts[name] = len(reports)

baseline = json.loads((root / 'verification/block11/MANIFEST_SHA256.json').read_text())
paths = ['lean-toolchain', 'lakefile.toml', 'lake-manifest.json']
paths += sorted(path for path in baseline if path.startswith('NSP14/') and path.endswith('.lean'))
paths += [path for _, path, _ in previous]
for path in paths:
    actual = hashlib.sha256((root / path).read_bytes()).hexdigest()
    if actual != baseline[path]:
        raise RuntimeError(('Predecessor or fixed environment changed', path))

record = {
    'status': 'PASS_COMPILED_RUN12_COORDINATE_CLOSURE', 'date_jst': '2026-11-10',
    'checks': records, 'axiom_report_counts': counts,
    'run12_declarations': declarations,
    'run12_test_declarations': test_declarations,
    'run12_theorem_count': sum(d['kind'] == 'theorem' for d in declarations),
    'allowed_axioms': sorted(allowed), 'new_mathematical_axioms': [],
    'predecessor_sources_tests_and_fixed_environment_match_block11': True,
    'predecessor_hash_count': len(paths), 'sources': sources,
    'paper_source': 'V02 section2; V03 O_COORD, algebraic semigroup-ring coordinate step',
    'scope': 'Actual non-x S0 acts on G/T/A/N/Q, generates A/Q in degree one. Opposite homogeneous jump filtrations on actual T/N, actual S0-linear same-jump quotient equivalence with inherited degree shift s. All terminal 2<=jump<=actual nu; deficit zero T=N=0. Literal formal k[[S]], actual maximal-ideal powers, and natural degree-preserving k-algebra comparison with algebraic G, transporting x/kernel/A/Q.',
    'paper_alignment_ledger': 'docs/LEAN_PAPER_ALIGNMENT_JA.md, A23-A27',
    'coordinate_closure': 'CLOSED_TASKS_1_TO_4',
    'remaining': ['actual stabilization and offset-volume/cut/tower resources; maximal Q2 to pair data',
                  'Koszul/Tor, target Betti input and full P14'],
}
(out / 'verification.json').write_text(json.dumps(record, indent=2) + '\n')
print('PASS', len(commands), 'commands;', sum(counts.values()), 'axiom reports;', len(paths), 'baseline hashes')
