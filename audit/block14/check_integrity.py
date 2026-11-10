#!/usr/bin/env python3
"""Check the pinned Run14 release, all prior source bytes, dependencies and ZIP."""
from pathlib import Path
import hashlib
import json
import subprocess
import zipfile

ROOT = Path(__file__).resolve().parents[2]
SUBMISSION = 'fbfa5debe3daa115b610ecc72dedc8fd52a817ca'
BASELINE = 'd8556dc615b1e1633379f4567e9e795b3f1c8ae3'
git = lambda *a: subprocess.check_output(['git', *a], cwd=ROOT)
sha = lambda b: hashlib.sha256(b).hexdigest()
blob = lambda p: git('show', f'{SUBMISSION}:{p}')

sources = git('diff', '--name-only', BASELINE, SUBMISSION, '--', 'NSP14').decode().splitlines()
tests = git('diff', '--name-only', BASELINE, SUBMISSION, '--', 'tests').decode().splitlines()
assert len(sources) == 49 and len(tests) == 7
for p in sources+tests:
    assert (ROOT/p).read_bytes() == blob(p), p
old = git('ls-tree', '-r', '--name-only', BASELINE).decode().splitlines()
frozen = [p for p in old if p.endswith('.lean') and
          (p.startswith('NSP14/') or p.startswith('tests/'))]
frozen += ['lean-toolchain', 'lakefile.toml', 'lake-manifest.json']
for p in frozen:
    assert (ROOT/p).read_bytes() == git('show', f'{BASELINE}:{p}') == blob(p), p
assert (ROOT/'NSP14.lean').read_bytes().startswith(git('show', f'{BASELINE}:NSP14.lean'))

submitted_hashes = json.loads(blob('verification/run14_continuation/SOURCE_SHA256.json'))
working_changes = []
for p, h in submitted_hashes.items():
    assert sha(blob(p)) == h, p
    if sha((ROOT/p).read_bytes()) != h:
        working_changes.append(p)
assert working_changes == ['scripts/verify_run14_continuation.py']

archive = ROOT/'artifacts/NS_P14_LEAN_RUN14_COMPLETE_20261110.zip'
assert archive.read_bytes() == blob(str(archive.relative_to(ROOT)))
assert sha(archive.read_bytes()) == archive.with_suffix('.sha256').read_text().split()[0]
with zipfile.ZipFile(archive) as z:
    names = z.namelist()
    assert len(names) == len(set(names))
    manifest = json.loads(z.read('MANIFEST_SHA256.json'))
    assert set(names) == set(manifest) | {'MANIFEST_SHA256.json'}
    for p, h in manifest.items():
        assert not Path(p).is_absolute() and '..' not in Path(p).parts
        data = z.read(p)
        assert sha(data) == h and data == blob(p), p
    assert z.testzip() is None

dependencies = []
for p in json.loads((ROOT/'lake-manifest.json').read_text())['packages']:
    d = ROOT/'.lake/packages'/p['name']
    head = subprocess.check_output(['git', '-C', str(d), 'rev-parse', 'HEAD'], text=True).strip()
    assert head == p['rev'], p['name']
    assert not subprocess.check_output(['git', '-C', str(d), 'diff', '--name-only'])
    assert not subprocess.check_output(['git', '-C', str(d), 'diff', '--cached', '--name-only'])
    dependencies.append(dict(name=p['name'], commit=head))

result = dict(status='PASS', submission=SUBMISSION, baseline=BASELINE,
              core_sources=49, core_lines=sum(len((ROOT/p).read_text().splitlines()) for p in sources),
              acceptance_sources=7, frozen_source_and_environment_files=len(frozen),
              final_manifest_entries=len(submitted_hashes), archive_entries=len(names),
              archive_payload_entries=len(manifest), archive_sha256=sha(archive.read_bytes()),
              only_pinned_working_difference=working_changes, dependencies=dependencies)
(ROOT/'audit/block14/integrity.json').write_text(json.dumps(result, indent=2)+'\n')
print(json.dumps(result, indent=2))
