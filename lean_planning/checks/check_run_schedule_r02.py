#!/usr/bin/env python3
"""Check roadmap coverage/order, not mathematical truth or run-count feasibility."""
from pathlib import Path
from collections import Counter
import json

root = Path(__file__).resolve().parents[2]
schedule = json.loads((root / 'lean_planning/run_schedule_r02.json').read_text())
registry = json.loads((root / schedule['registry_path']).read_text())['lemmas']
ids = {item['id'] for item in registry}
runs = schedule['runs']
assert [r['run'] for r in runs] == list(range(11, 21))
owners = {}
counts = Counter(x for r in runs for x in r['registry_closure_ownership'])
assert set(counts) == ids, {'missing': sorted(ids - set(counts)),
                           'unknown': sorted(set(counts) - ids)}
assert all(n == 1 for n in counts.values()), 'Duplicate closure ownership'
for run in runs:
    for item in run['registry_closure_ownership']:
        owners[item] = run['run']
refinements = {(r['consumer'], r['bundled_dependency']): r
               for r in schedule['dependency_refinements']}
used_refinements = []
edges = 0
for item in registry:
    for dep in item['depends_on']:
        edges += 1
        if owners[dep] > owners[item['id']]:
            refinement = refinements.get((item['id'], dep))
            assert refinement is not None, (item['id'], dep, 'Unscheduled prerequisite')
            assert refinement['provider_run'] <= owners[item['id']]
            assert refinement['aggregate_closure_run'] == owners[dep]
            assert refinement['required_export'] and refinement['reason']
            used_refinements.append(refinement)

# Within-run prerequisites still need a real topological execution order.
remaining = {item['id']: set(item['depends_on']) for item in registry}
order = []
while remaining:
    available = sorted(k for k, deps in remaining.items() if not deps)
    assert available, 'Registry dependency cycle'
    for item in available:
        order.append(item)
        remaining.pop(item)
    for deps in remaining.values():
        deps.difference_update(available)
published = schedule['published_inputs']
assert len(published) == 7 and set(published) <= set(owners)
assert owners['I_MAIN'] == schedule['counting']['target_total_runs'] == 20
assert schedule['counting']['next_new_run'] == 12
result = {
    'status': 'PASS_STRUCTURAL_PLAN_CHECK_ONLY',
    'registry_ids_covered_once': len(ids),
    'registry_dependency_edges_checked': edges,
    'published_inputs_with_owners': {item: owners[item] for item in published},
    'coarse_dependency_refinements_requiring_actual_proofs': used_refinements,
    'within_run_topological_order': {
        str(r['run']): [x for x in order if owners[x] == r['run']] for r in runs},
    'not_certified': ['Mathematical correctness', '20-run feasibility',
                      'Implementation or proof completion',
                      'Sufficiency of the scoped X_BASIC export'],
}
(root / 'lean_planning/run_schedule_r02_check.json').write_text(
    json.dumps(result, ensure_ascii=False, indent=2) + '\n')
print('PASS: 50 registry IDs, 7 published inputs, ownership and dependency structure; '
      'one explicit scoped X_BASIC export remains a proof obligation.')
