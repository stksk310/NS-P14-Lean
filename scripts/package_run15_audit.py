#!/usr/bin/env python3
"""Package the explicitly partial Run15 source/evidence snapshot after verification."""
from pathlib import Path
import hashlib,json,zipfile
root=Path(__file__).resolve().parents[1]
out=root/'verification/run15'
verified=json.loads((out/'verification.json').read_text())
assert verified['status']=='PASS_IMPLEMENTED_EXPORTS_ONLY_NOT_RUN15_COMPLETE'
assert verified['fresh_project_test_cache'] is True and verified['unresolved_goals_proved'] is False
status=json.loads((root/'docs/RUN15_CLOSURE_STATUS.json').read_text())
assert status['status']=='PARTIAL_NOT_RUN15_COMPLETE' and status['run15_complete'] is False
for name,digest in json.loads((out/'SOURCE_SHA256.json').read_text()).items():
    assert hashlib.sha256((root/name).read_bytes()).hexdigest()==digest,name
paths=set()
for directory in ['NSP14','tests','audit']:
    paths.update(str(p.relative_to(root)) for p in (root/directory).rglob('*.lean'))
paths.update(['NSP14.lean','lean-toolchain','lakefile.toml','lake-manifest.json',
    'scripts/verify_run15.py','scripts/package_run15_audit.py','docs/LEAN_PAPER_ALIGNMENT_JA.md'])
paths.update(str(p.relative_to(root)) for p in (root/'docs').glob('RUN15*') if p.is_file())
paths.add('docs/superpowers/plans/2026-11-10-run15-actual-tor-target-ordinary-order.md')
paths.update(str(p.relative_to(root)) for p in out.rglob('*') if p.is_file() and p.name!='MANIFEST_SHA256.json')
manifest={p:hashlib.sha256((root/p).read_bytes()).hexdigest() for p in sorted(paths)}
(out/'MANIFEST_SHA256.json').write_text(json.dumps(manifest,ensure_ascii=False,indent=2)+'\n')
paths.add('verification/run15/MANIFEST_SHA256.json')
artifact=root/'artifacts/NS_P14_LEAN_RUN15_PARTIAL_20261110.zip'
artifact.parent.mkdir(parents=True,exist_ok=True)
with zipfile.ZipFile(artifact,'w',zipfile.ZIP_DEFLATED) as z:
    for path in sorted(paths):z.write(root/path,path)
with zipfile.ZipFile(artifact) as z:
    assert z.testzip() is None
    for path,digest in manifest.items():assert hashlib.sha256(z.read(path)).hexdigest()==digest,path
sha=hashlib.sha256(artifact.read_bytes()).hexdigest()
artifact.with_suffix('.sha256').write_text(sha+'  '+artifact.name+'\n')
print(json.dumps(dict(status='PACKAGED_PARTIAL_NOT_COMPLETE',files=len(paths),zip=str(artifact.relative_to(root)),bytes=artifact.stat().st_size,sha256=sha),indent=2))
