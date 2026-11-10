#!/usr/bin/env python3
"""Independently check the final release snapshot and its packaged bytes."""
from pathlib import Path
import hashlib
import json
import subprocess
import zipfile

ROOT = Path(__file__).resolve().parents[2]
REPO = Path('/workspace/NS-P14-Lean')
COMMIT = 'd8556dc615b1e1633379f4567e9e795b3f1c8ae3'
BASELINE = '6b8d16889ea9b4d88567f0d9ac70391db2a49824'
sha = lambda data: hashlib.sha256(data).hexdigest()
git = lambda *args: subprocess.check_output(['git', '-C', str(REPO), *args])

sources = json.loads((ROOT/'verification/block13_continuation/SOURCE_SHA256.json').read_text())
assert sources
for name, digest in sources.items():
    assert sha((ROOT/name).read_bytes()) == digest, name
    assert (ROOT/name).read_bytes() == git('show', f'{COMMIT}:{name}'), name

baseline = json.loads((ROOT/'verification/block12/MANIFEST_SHA256.json').read_text())
frozen = sorted(p for p in baseline if p.endswith('.lean') and
                (p.startswith('NSP14/') or p.startswith('tests/')))
frozen += ['lean-toolchain', 'lakefile.toml', 'lake-manifest.json']
for name in frozen:
    assert (ROOT/name).read_bytes() == git('show', f'{BASELINE}:{name}'), name
    assert (ROOT/name).read_bytes() == git('show', f'{COMMIT}:{name}'), name

archive = ROOT/'artifacts/NS_P14_LEAN_RUN13_COMPLETE_20261110.zip'
assert sha(archive.read_bytes()) == archive.with_suffix('.sha256').read_text().split()[0]
with zipfile.ZipFile(archive) as bundle:
    names = bundle.namelist()
    assert len(names) == len(set(names))
    manifest = json.loads(bundle.read('MANIFEST_SHA256.json'))
    assert set(names) == set(manifest) | {'MANIFEST_SHA256.json'}
    for name, digest in manifest.items():
        assert not Path(name).is_absolute() and '..' not in Path(name).parts
        data = bundle.read(name)
        assert sha(data) == digest, name
        assert data == (ROOT/name).read_bytes(), name
        assert data == git('show', f'{COMMIT}:{name}'), name

deps = json.loads((ROOT/'lake-manifest.json').read_text())
dep_results = []
for package in deps['packages']:
    dep = ROOT/'.lake/packages'/package['name']
    actual = subprocess.check_output(['git', '-C', str(dep), 'rev-parse', 'HEAD'], text=True).strip()
    assert actual == package['rev'], (package['name'], actual)
    # Build products are ignored; tracked dependency source must be pristine.
    assert not subprocess.check_output(['git', '-C', str(dep), 'diff', '--name-only'])
    assert not subprocess.check_output(['git', '-C', str(dep), 'diff', '--cached', '--name-only'])
    dep_results.append({'name': package['name'], 'commit': actual})

result = dict(status='PASS', commit=COMMIT, baseline=BASELINE,
              final_source_hashes=len(sources), frozen_source_and_environment_files=len(frozen),
              archive_entries=len(names), archive_manifest_entries=len(manifest),
              archive_sha256=sha(archive.read_bytes()), dependencies=dep_results)
(ROOT/'audit/block13/integrity.json').write_text(json.dumps(result, indent=2)+'\n')
print(json.dumps(result, indent=2))
