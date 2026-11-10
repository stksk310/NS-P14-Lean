#!/usr/bin/env python3
"""Recheck actual numerical-semigroup foundations and Blocks 01–07."""
from pathlib import Path
import hashlib
import json
import re
import subprocess
import time

root = Path(__file__).resolve().parents[1]
out = root / 'verification/block08'
out.mkdir(parents=True, exist_ok=True)
commands = [
    ('build', ['lake', 'build']),
    ('basic_recheck', ['lake', 'env', 'lean', 'NSP14/Semigroup/Basic.lean']),
    ('apery_recheck', ['lake', 'env', 'lean', 'NSP14/Semigroup/Apery.lean']),
    ('atoms_recheck', ['lake', 'env', 'lean', 'NSP14/Semigroup/Atoms.lean']),
    ('order_recheck', ['lake', 'env', 'lean', 'NSP14/Semigroup/Order.lean']),
    ('aperygrading_recheck', ['lake', 'env', 'lean', 'NSP14/Semigroup/AperyGrading.lean']),
    ('heads_recheck', ['lake', 'env', 'lean', 'NSP14/Semigroup/Heads.lean']),
    ('tests_and_axioms', ['lake', 'env', 'lean', 'tests/SemigroupFoundations.lean']),
    ('block01_regression', ['lake', 'env', 'lean', 'tests/SmallScalar.lean']),
    ('block02_regression', ['lake', 'env', 'lean', 'tests/Sidon.lean']),
    ('block03_regression', ['lake', 'env', 'lean', 'tests/Resources.lean']),
    ('block04_regression', ['lake', 'env', 'lean', 'tests/LowRank.lean']),
    ('block05_regression', ['lake', 'env', 'lean', 'tests/LargeSeed.lean']),
    ('block06_regression', ['lake', 'env', 'lean', 'tests/LargeScalar.lean']),
    ('block07_regression', ['lake', 'env', 'lean', 'tests/OrdinaryNumerical.lean']),
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
theorem_names = [
    'zero_mem', 'add_mem', 'multiple_mem', 'positive_exists',
    'multiplicity_spec', 'multiplicity_pos', 'multiplicity_mem', 'multiplicity_le',
    'multiplicity_eq', 'multiplicity_le_conductor', 'residue_exists', 'apery_spec',
    'apery_mem', 'apery_mod', 'apery_min', 'apery_injective',
    'apery_card', 'mem_aperySet_iff', 'apery_le', 'decomposition',
    'decomposition_unique', 'apery_add_multiple', 'zero_min', 'zero_mem_apery',
    'multiplicity_not_apery', 'apery_no_predecessor', 'mem_apery_iff_no_predecessor', 'multiplicity_atom',
    'atom_apery', 'mem_atoms_iff', 'multiplicity_mem_atoms', 'atoms_mem',
    'mem_closure_atoms', 'closure_atoms', 'atom_mem_of_generates', 'embeddingDimension_pos',
    'embeddingDimension_le_multiplicity', 'nonmultiplicity_atoms_card', 'nonmultiplicity_atoms_apery', 'sum_mem',
    'length_zero', 'length_one', 'length_le', 'length_multiplicity_bound',
    'length_exists', 'order_length', 'length_le_order', 'order_bound',
    'order_zero', 'order_pos', 'order_eq_zero_iff', 'length_add',
    'order_add', 'order_multiplicity', 'order_add_multiplicity', 'atom_length_bound',
    'atom_order', 'order_one_iff_atom', 'order_sum', 'longest_factors_atoms',
    'order_realized_by_atoms', 'atomic_length_le', 'degree_zero', 'degree_one',
    'degree_zero_card', 'degree_one_card', 'lowSet_subset', 'lowSet_card',
    'highSet_eq_sdiff', 'highSet_card', 'degree_two_le_deficit', 'multiplicity_eq_embedding_add_deficit',
    'apery_summands', 'apery_predecessor_order', 'degree_exists_le', 'apery_order_bound',
    'terminal_iff_head', 'head_predecessor', 'head_sub_terminal', 'terminal_pos',
    'terminal_jump', 'terminal_head_degree', 'jump_le_of_live_base', 'jump_le_of_live_head',
    'live_iff_of_equal_jump',
]
expected = {'NSP14.NumericalSemigroup.' + name for name in theorem_names}
expected.add('NSP14.NumericalSemigroup.terminalHeadEquiv')
counts = {}
for name, count in [('tests_and_axioms', 86), ('block01_regression', 10),
                    ('block02_regression', 14), ('block03_regression', 7), ('block04_regression', 13),
                    ('block05_regression', 22), ('block06_regression', 15),
                    ('block07_regression', 25)]:
    text = (out / (name + '.log')).read_text()
    reports = re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]", text, re.S)
    if len(reports) != count:
        raise RuntimeError(('Unexpected axiom report count', name, len(reports)))
    if name == 'tests_and_axioms' and {theorem for theorem, _ in reports} != expected:
        raise RuntimeError('Block08 axiom report names do not match the public theorems')
    for theorem, group in reports:
        actual = {v.strip() for v in group.split(',') if v.strip()}
        if not actual <= allowed:
            raise RuntimeError(('Unexpected axiom', theorem, actual - allowed))
    counts[name] = len(reports)

baseline = json.loads((root / 'verification/block07/MANIFEST_SHA256.json').read_text())
paths = [
    'lean-toolchain',
    'lakefile.toml',
    'lake-manifest.json',
    'NSP14/Ordinary/LargeScalar.lean',
    'NSP14/Ordinary/LargeSeed.lean',
    'NSP14/Ordinary/LowRank.lean',
    'NSP14/Ordinary/NumericalClosure.lean',
    'NSP14/Ordinary/Resources.lean',
    'NSP14/Ordinary/Scalarization.lean',
    'NSP14/Ordinary/SmallScalar.lean',
    'NSP14/Ordinary/TargetMargin.lean',
    'NSP14/Combinatorics/Sidon.lean',
    'tests/SmallScalar.lean',
    'tests/Sidon.lean',
    'tests/Resources.lean',
    'tests/LowRank.lean',
    'tests/LargeSeed.lean',
    'tests/LargeScalar.lean',
    'tests/OrdinaryNumerical.lean',
]
for path in paths:
    actual = hashlib.sha256((root / path).read_bytes()).hexdigest()
    if actual != baseline[path]:
        raise RuntimeError(('Predecessor or fixed environment changed', path))

record = {
    'status': 'PASS_COMPILED_BLOCK08', 'date_jst': '2026-11-10',
    'checks': records, 'axiom_report_counts': counts,
    'block08_declarations': sorted(expected),
    'block08_theorem_count': len(theorem_names),
    'proof_bearing_definition_count': 1,
    'allowed_axioms': sorted(allowed),
    'new_mathematical_axioms': [],
    'predecessor_sources_tests_and_fixed_environment_match_block07': True,
    'sources': ['NSP14/Semigroup/Basic.lean', 'NSP14/Semigroup/Apery.lean', 'NSP14/Semigroup/Atoms.lean', 'NSP14/Semigroup/Order.lean', 'NSP14/Semigroup/AperyGrading.lean', 'NSP14/Semigroup/Heads.lean'],
    'paper_source': 'proof_integrated_v2/NS_P14_INTEGRATED_PROOF_JA.md, section2 actual numerical Apery coordinates; V03 O_COORD numerical foundations; SO1 atom input',
    'scope': 'Cofinite additive submonoids yield actual multiplicity, unique finite Apery decomposition, minimal atom generators, maximal atomic order, degree counts and numerical terminal/head bijection. No actual tangent-cone ring identification yet.',
    'paper_alignment_ledger': 'docs/LEAN_PAPER_ALIGNMENT_JA.md, A10-A11',
    'remaining': ['actual semigroup-ring/completion tangent-cone identification',
                  'Q=A/N and equal-jump module isomorphisms, jump upper bound',
                  'actual offset-volume/cut/tower resource construction',
                  'maximal Q2 to pair data, Tor/Betti and full P14'],
}
(out / 'verification.json').write_text(json.dumps(record, indent=2) + '\n')
print(json.dumps(record, indent=2))
