#!/usr/bin/env python3
"""Read-only cross-check of final independent validation against published R16."""
import gzip, hashlib, json, pathlib, subprocess
root = pathlib.Path(__file__).resolve().parents[2]
fresh = root / 'verification/run18/runs/independent_final_audit_20261115_r01'
release = root / 'verification/run18/runs/release_candidate_20261115_r16'
load = lambda p: json.loads(p.read_text())
sha = lambda b: hashlib.sha256(b).hexdigest()
s = load(fresh / 'verification.json')
assert s['status'] == 'PASS_RUN18_COMPLETE_VALIDATION' and s['run18_complete']
assert not s['expected_open_acceptances'] and not s['unproved_ids']
assert len(s['checks']) == 280 and all(x['passed'] and x['exit_code'] == 0 for x in s['checks'])
assert sum(x['name'].startswith('fixture_') for x in s['checks']) == 268
for directory in [fresh, release]:
    for rel, digest in load(directory / 'MANIFEST_SHA256.json').items():
        assert sha((root / rel).read_bytes()) == digest, rel
    for rel, digest in load(directory / 'SOURCE_SHA256.json').items():
        assert sha((root / rel).read_bytes()) == digest, rel
with gzip.open(fresh / 'declarations.json.gz', 'rt') as f: a = json.load(f)
with gzip.open(release / 'declarations.json.gz', 'rt') as f: b = json.load(f)
byname = lambda rows: {r['name']: r for r in rows}
assert len(byname(a)) == len(a) == 10662
assert byname(a) == byname(b), 'Fresh declarations/types/dependencies differ from published R16'
assert sum('explicit_type' in r for r in a) == 2421
allowed = {'Classical.choice', 'Quot.sound', 'propext'}
assert all(set(r['axioms']) <= allowed and r['name'] not in r['axioms'] for r in a)
assert sha((root / 'audit/run18/RequestedGoals.lean').read_bytes()) == s['frozen_requested_goals_sha256']
changed = subprocess.check_output(['git', 'diff', '--name-only', s['baseline_commit'], s['proof_snapshot_commit'], '--', 'NSP14'], cwd=root, text=True).splitlines()
production = [p for p in changed if p.endswith('.lean')]
build = (fresh / 'build.log').read_text()
assert len(production) == 141
assert all('Built ' + p[:-5].replace('/', '.') + ' ' in build for p in production)
old_report_files = subprocess.check_output(['git', 'ls-tree', '-r', '--name-only', '47aeeb4359f5af1559a40a6e0a489d86a3f5bc87', '--', 'audit/run18_independent'], cwd=root, text=True).splitlines()
for rel in old_report_files:
    old = subprocess.check_output(['git', 'show', f'47aeeb4359f5af1559a40a6e0a489d86a3f5bc87:{rel}'], cwd=root)
    assert (root / rel).read_bytes() == old, rel
print(json.dumps({'status': 'PASS', 'target': s['proof_snapshot_commit'], 'checks': len(s['checks']), 'fixtures': 268, 'fresh_built_production_modules': len(production), 'declarations_identical_to_published_r16': len(a), 'explicit_new_types': 2421, 'prior_audit_files_preserved': len(old_report_files), 'prior_evidence_preserved_by_verifier': s['preserved_evidence_count'], 'command_seconds': round(sum(x['seconds'] for x in s['checks']), 3), 'closed_ids': s['closed_ids'], 'unproved_ids': s['unproved_ids'], 'allowed_axioms': sorted(allowed)}, ensure_ascii=False, indent=2))
