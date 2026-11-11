#!/usr/bin/env python3
"""Check committed Run15 evidence and complete ZIP against the audited commit."""
from io import BytesIO
from pathlib import Path
import gzip
import hashlib
import json
import re
import subprocess
import zipfile

ROOT = Path(__file__).resolve().parents[2]
BASE = '20aadbf7011692eb3bfffef49029e2c5e416ef3d'
AUDITED = '447b7ae782414b739968a2a3009dd3a52ae230d0'


def git(*args):
    return subprocess.check_output(['git', *args], cwd=ROOT)


def original(path):
    return git('show', AUDITED+':'+path)


def main():
    changed = git('diff', '--name-only', BASE, AUDITED, '--', 'NSP14').decode().splitlines()
    assert len(changed) == 215
    assert all(git('diff', '--name-status', BASE, AUDITED, '--', p).startswith(b'A\t')
               for p in changed)
    rootimports = original('NSP14.lean').decode()
    for path in changed:
        text = original(path).decode()
        assert 'public import '+path[:-5].replace('/', '.') in rootimports, path
        assert all(line.rstrip() == line for line in text.splitlines()), path
        assert not re.search(r'\b(?:sorry|admit|sorryAx|native_decide|unsafe|implemented_by|extern|initialize|run_elab|elab_rules|skipKernelTC)\b|^\s*(?:private\s+|public\s+)?axiom\b', text, re.M), path
        assert not re.search(r'^\s*(?:public\s+)?import\s+audit\.', text, re.M), path
    goal_commits = git('log', AUDITED, '--format=%H', '--', 'audit/run15/RemainingGoals.lean').decode().splitlines()
    assert len(goal_commits) == 1
    scan = dict(status='PASS_SOURCE_SCOPE_SCAN', source_files=len(changed),
                all_new_sources_imported=True, forbidden_proof_or_metaprogramming_constructs=[],
                production_imports_audit=False, original_goals_changed_after_creation=False,
                original_goals_creation_commit=goal_commits[0])
    Path(__file__).with_name('source_scope_scan.json').write_text(json.dumps(scan, indent=2)+'\n')
    sourcehash = json.loads(original('verification/run15_closure/SOURCE_SHA256.json'))
    for path, digest in sourcehash.items():
        assert hashlib.sha256(original(path)).hexdigest() == digest, path
    artifact = 'artifacts/NS_P14_LEAN_RUN15_COMPLETE_20261110.zip'
    raw = original(artifact)
    digest = hashlib.sha256(raw).hexdigest()
    assert original(artifact[:-4]+'.sha256').decode().split()[0] == digest
    with zipfile.ZipFile(BytesIO(raw)) as bundle:
        assert bundle.testzip() is None
        names = bundle.namelist()
        assert len(names) == len(set(names))
        manifest = json.loads(bundle.read('verification/run15_closure/MANIFEST_SHA256.json'))
        assert set(names) == set(manifest) | {'verification/run15_closure/MANIFEST_SHA256.json'}
        for path, expected in manifest.items():
            data = bundle.read(path)
            assert hashlib.sha256(data).hexdigest() == expected, path
            assert data == original(path), ('ZIP/commit difference', path)
    declarations = json.loads(gzip.decompress(original('verification/run15_closure/declarations.json.gz')))
    allowed = {'propext', 'Classical.choice', 'Quot.sound'}
    assert all(set(d['axioms']) <= allowed and d['name'] not in d['axioms'] for d in declarations)
    core = [d for d in declarations if d['source'] in changed]
    assert all('explicit_type' in d for d in core)
    result = dict(status='PASS_COMMITTED_PROVENANCE_CHECKS', audited_commit=AUDITED,
                  source_files=len(changed), source_lines=sum(len(original(p).splitlines()) for p in changed),
                  bound_source_hashes=len(sourcehash), zip_entries=len(names), zip_sha256=digest,
                  recorded_environment_declarations=len(declarations), recorded_core_declarations=len(core),
                  allowed_axioms=sorted(allowed),
                  notes='Committed evidence checked for integrity; fresh replay is separate.')
    Path(__file__).with_name('provenance_checks.json').write_text(json.dumps(result, indent=2)+'\n')
    print(result['status'], len(changed), 'core files,', len(names), 'ZIP entries')


if __name__ == '__main__':
    main()
