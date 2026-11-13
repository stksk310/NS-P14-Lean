#!/usr/bin/env python3
"""Integrity and source-scope checks against the fixed published Run16 SHA."""
from io import BytesIO
from pathlib import Path
import gzip
import hashlib
import json
import re
import subprocess
import zipfile

ROOT = Path(__file__).resolve().parents[2]
BASE = '447b7ae782414b739968a2a3009dd3a52ae230d0'
AUDITED = '584f92d8c1a7fc1e2413f606b661fc9b81f472cd'


def git(*args):
    return subprocess.check_output(['git', *args], cwd=ROOT)


def original(path):
    return git('show', AUDITED+':'+path)


def main():
    files = git('diff', '--name-only', BASE, AUDITED, '--', 'NSP14').decode().splitlines()
    assert len(files) == 116
    assert all(git('diff', '--name-status', BASE, AUDITED, '--', p).startswith(b'A\t') for p in files)
    imports = original('NSP14.lean').decode()
    for path in files:
        text = original(path).decode()
        assert 'public import '+path[:-5].replace('/', '.') in imports, path
        assert all(s.rstrip() == s for s in text.splitlines()), path
        assert not re.search(r'\b(?:sorry|admit|sorryAx|native_decide|unsafe|implemented_by|extern|initialize|run_elab|elab_rules|skipKernelTC)\b|^\s*(?:private\s+|public\s+)?axiom\b', text, re.M), path
        assert not re.search(r'^\s*(?:public\s+)?import\s+audit\.', text, re.M), path
    hashes = json.loads(original('verification/run16/final/SOURCE_SHA256.json'))
    for path, expected in hashes.items():
        assert hashlib.sha256(original(path)).hexdigest() == expected, path
    evidence = json.loads(original('verification/run16/final/MANIFEST_SHA256.json'))
    for path, expected in evidence.items():
        assert hashlib.sha256(original(path)).hexdigest() == expected, path
    artifact = 'artifacts/NS_P14_RUN16_COMPLETE_AUDIT_20261111.zip'
    raw = original(artifact)
    digest = hashlib.sha256(raw).hexdigest()
    assert digest == original(artifact+'.sha256').decode().split()[0]
    with zipfile.ZipFile(BytesIO(raw)) as z:
        assert z.testzip() is None
        names = z.namelist()
        assert len(names) == len(set(names))
        manifest = json.loads(z.read('AUDIT_MANIFEST_SHA256.json'))
        assert set(names) == set(manifest) | {'AUDIT_MANIFEST_SHA256.json', 'BASELINE.txt'}
        for path, expected in manifest.items():
            data = z.read(path)
            assert hashlib.sha256(data).hexdigest() == expected, path
            assert data == original(path), ('ZIP/commit difference', path)
        assert BASE in z.read('BASELINE.txt').decode()
    declarations = json.loads(gzip.decompress(original('verification/run16/final/declarations.json.gz')))
    allowed = {'propext', 'Classical.choice', 'Quot.sound'}
    assert all(set(d['axioms']) <= allowed and d['name'] not in d['axioms'] for d in declarations)
    core = [d for d in declarations if d['source'] in files]
    assert all('explicit_type' in d for d in core)
    result = dict(status='PASS_COMMITTED_PROVENANCE_AND_SOURCE_SCOPE', audited_commit=AUDITED,
                  baseline_commit=BASE, source_files=len(files),
                  source_lines=sum(len(original(p).splitlines()) for p in files),
                  old_production_files_changed=0, all_new_sources_root_imported=True,
                  forbidden_proof_or_metaprogramming_constructs=[], production_imports_audit=False,
                  bound_source_hashes=len(hashes), bound_evidence_hashes=len(evidence),
                  zip_entries=len(names), zip_manifest_entries=len(manifest), zip_sha256=digest,
                  recorded_environment_declarations=len(declarations), core_declarations=len(core),
                  type_records=sum('explicit_type' in d for d in declarations),
                  allowed_axioms=sorted(allowed), note='Committed integrity checked; fresh Lean replay is separate.')
    Path(__file__).with_name('provenance_checks.json').write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
