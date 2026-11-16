#!/usr/bin/env python3
"""Verify proved Run13 exports; deliberately does NOT certify completion of Run13."""
from pathlib import Path
import hashlib
import json
import re
import subprocess
import time

root = Path(__file__).resolve().parents[1]
out = root / 'verification/block13'
out.mkdir(parents=True, exist_ok=True)
baseline = json.loads((root / 'verification/block12/MANIFEST_SHA256.json').read_text())
sources = sorted(str(p.relative_to(root)) for p in (root / 'NSP14/Homological').glob('*.lean'))
new_tests = ['tests/Run13Fixtures.lean', 'tests/KoszulPresentation.lean', 'tests/KoszulComplex.lean',
             'tests/KoszulFiniteModules.lean', 'tests/KoszulTor.lean', 'tests/KoszulActual.lean',
             'tests/BettiBaseChange.lean', 'tests/StandardMonomials.lean']
actual_sources = sorted(str(p.relative_to(root)) for p in (root / 'NSP14').rglob('*.lean')
                        if str(p.relative_to(root)) not in baseline)
actual_tests = sorted(str(p.relative_to(root)) for p in (root / 'tests').glob('*.lean')
                      if str(p.relative_to(root)) not in baseline)
if actual_sources != sources or actual_tests != sorted(new_tests + ['tests/Run13Axioms.lean']):
    raise RuntimeError(('Unregistered new Lean files', actual_sources, actual_tests))

def collect(path):
    namespaces, result = [], []
    for line in (root / path).read_text().splitlines():
        match = re.match(r'^namespace (\S+)', line)
        if match:
            namespaces.append(match[1]); continue
        match = re.match(r'^end(?: (\S+))?$', line)
        if match and namespaces and match[1] == namespaces[-1]:
            namespaces.pop(); continue
        match = re.match(r'^(?:noncomputable )?(def|abbrev|theorem|instance) (\w+)', line)
        if match:
            result.append({'kind': match[1], 'name': '.'.join(namespaces + [match[2]]), 'source': path})
    return result

inventory = {'core': [d for p in sources for d in collect(p)],
             'test_fixtures': [d for p in new_tests for d in collect(p)]}
if inventory != json.loads((out / 'declarations.json').read_text()):
    raise RuntimeError('Current declaration inventory differs from axiom audit inventory')
for path in sources + new_tests:
    if re.search(r'\b(?:sorry|admit|sorryAx|native_decide)\b|^axiom\b', (root / path).read_text(), re.M):
        raise RuntimeError(('Unproved or unapproved proof mechanism', path))

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
run12_tests = ['tests/Run12BasicExamples.lean', 'tests/Run12Fixtures.lean', 'tests/JumpBounds.lean',
               'tests/PolynomialAction.lean', 'tests/JumpStrata.lean', 'tests/CompletedComparison.lean']
def compile_test(path):
    target = root / '.lake/build/lib/lean' / Path(path).with_suffix('.olean')
    target.parent.mkdir(parents=True, exist_ok=True)
    return ['lake', 'env', 'lean', path, '-o', str(target)]
commands = [('build', ['lake', 'build'])]
commands += [(Path(p).stem.lower() + '_recheck', ['lake', 'env', 'lean', p]) for p in sources]
commands += [(name, compile_test(p)) for name, p, _ in previous]
commands += [(Path(p).stem.lower() + '_run12', compile_test(p)) for p in run12_tests]
commands += [('run12_axioms', ['lake', 'env', 'lean', 'tests/Run12Axioms.lean'])]
commands += [(Path(p).stem.lower() + '_acceptance', compile_test(p)) for p in new_tests]
commands += [('run13_axioms', ['lake', 'env', 'lean', 'tests/Run13Axioms.lean']),
             ('declaration_types', ['lake', 'env', 'lean', 'verification/block13/DeclarationTypes.lean']),
             ('run_schedule', ['python3', 'lean_planning/checks/check_run_schedule_r02.py']),
             ('block01_domain_checks', ['lake', 'env', 'lean', 'audit/DomainChecks.lean']),
             ('block02_assumption_checks', ['lake', 'env', 'lean', 'audit/block02/AssumptionChecks.lean'])]
records = []
for name, cmd in commands:
    start = time.monotonic()
    result = subprocess.run(cmd, cwd=root, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    (out / (name + '.log')).write_text(result.stdout)
    records.append({'command': cmd, 'exit_code': result.returncode, 'seconds': round(time.monotonic()-start, 3)})
    print(name, 'exit', result.returncode, flush=True)
    if result.returncode:
        print(result.stdout); raise SystemExit(result.returncode)
    if re.search(r'\bwarning:', result.stdout):
        raise RuntimeError(('Warning in verification', name, result.stdout))

allowed = {'propext', 'Classical.choice', 'Quot.sound'}
expected = {d['name'] for group in inventory.values() for d in group}
counts = {}
for name, count in [('run13_axioms', len(expected)), ('run12_axioms', 298)] + [(n, c) for n, _, c in previous]:
    output = (out / (name + '.log')).read_text()
    reports = re.findall(r"'([^']+)' (?:depends on axioms:\s*\[([^]]*)\]|does not depend on any axioms)", output, re.S)
    if len(reports) != count:
        raise RuntimeError(('Unexpected report count', name, len(reports), count))
    if name == 'run13_axioms' and {decl for decl, _ in reports} != expected:
        raise RuntimeError('Run13 audit omits or duplicates declarations')
    for decl, group in reports:
        axioms = {a.strip() for a in group.split(',') if a.strip()}
        if not axioms <= allowed:
            raise RuntimeError(('Unexpected axiom dependency', decl, axioms-allowed))
    counts[name] = len(reports)

paths = sorted(p for p in baseline if ((p.startswith('NSP14/') or p.startswith('tests/')) and p.endswith('.lean')))
paths += ['lean-toolchain', 'lakefile.toml', 'lake-manifest.json']
for p in paths:
    if hashlib.sha256((root / p).read_bytes()).hexdigest() != baseline[p]:
        raise RuntimeError(('Predecessor or fixed dependency changed', p))
summary = {
    'status': 'PASS_PROVED_EXPORTS_RUN13_INCOMPLETE', 'date_jst': '2026-11-10',
    'run13_complete': False, 'X_BASIC_closed': False, 'I_FIELD_closed': False,
    'baseline_commit': '6b8d16889ea9b4d88567f0d9ac70391db2a49824',
    'checks': records, 'axiom_report_counts': counts,
    'allowed_axioms': sorted(allowed), 'new_mathematical_axioms': [],
    'predecessor_sources_tests_and_fixed_environment_match_block12': True,
    'predecessor_hash_count': len(paths), 'sources': sources,
    'core_declarations': inventory['core'], 'test_declarations': inventory['test_fixtures'],
    'core_theorem_count': sum(d['kind']=='theorem' for d in inventory['core']),
    'core_line_count': sum(len((root/p).read_text().splitlines()) for p in sources),
    'paper_alignment': 'docs/LEAN_PAPER_ALIGNMENT_JA.md, A28-A33',
    'remaining_declarations': 'docs/RUN13_REMAINING_DECLARATIONS_JA.md',
    'recalibration': 'docs/RUN13_20RUN_RECALIBRATION_JA.md',
    'scope': 'Actual full-atom minimal graded presentation; concrete variable Koszul and genuine finite free residue resolution; ordinary Tor objectwise comparison; all-variable null-homotopy and finite coefficient homology; total Betti/free Betti and actual completed/same-jump transport; standard quotient monomial basis/unit minors; generic short-exact-complex rank identities and flat vector-complex homology base change.',
    'not_certified': ['Tor comparison naturality/minimal-resolution balancing and ranks',
                      'graded Koszul/Betti finite support and same-jump homology shift',
                      'Koszul preservation of short exact sequences and bounded-filtered comparison',
                      'actual changed-polynomial-module base change/Betti preservation and actual G base change',
                      'residue binomial and square quotient numerical Betti acceptance examples',
                      'initial/block rank bridge and full P14'],
}
(out/'verification.json').write_text(json.dumps(summary, ensure_ascii=False, indent=2)+'\n')
print('PASS_PROVED_EXPORTS_RUN13_INCOMPLETE',len(commands),'commands;',sum(counts.values()),'axiom reports;',len(paths),'baseline hashes')
