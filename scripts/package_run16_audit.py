#!/usr/bin/env python3
"""Package the verified Run16 source and evidence, without altering older audit bundles."""
from pathlib import Path
import hashlib,json,subprocess,zipfile
root=Path(__file__).resolve().parents[1]
status=json.loads((root/'docs/RUN16_CLOSURE_STATUS.json').read_text())
assert status['status']=='COMPLETE'and status['run16_complete']and status['unproved_ids']==[]
verified=json.loads((root/'verification/run16/final/verification.json').read_text())
assert verified['status']=='PASS_RUN16_PROOF_CLOSURE'
review=json.loads((root/'verification/run16/final_review.json').read_text())
assert review['gate']=='PASS'and review['fresh_context']
for p,h in json.loads((root/'verification/run16/final/SOURCE_SHA256.json').read_text()).items():
    assert hashlib.sha256((root/p).read_bytes()).hexdigest()==h,('source mismatch',p)
for p,h in json.loads((root/'verification/run16/final/MANIFEST_SHA256.json').read_text()).items():
    assert hashlib.sha256((root/p).read_bytes()).hexdigest()==h,('evidence mismatch',p)
files=set(verified['sources']+verified['acceptance_tests']+[verified['closure_contract'],'NSP14.lean',
    'README.md','LEAN_PROGRESS.md','docs/LEAN_PAPER_ALIGNMENT_JA.md',
    'lean-toolchain','lakefile.toml','lake-manifest.json','scripts/verify_run16.py','scripts/check_run16_coordinates.py',
    'scripts/package_run16_audit.py','docs/superpowers/plans/2026-11-10-run16-endpoint-kernel-transfer-order.md'])
files.update(str(p.relative_to(root))for p in(root/'docs').glob('RUN16*')if p.is_file())
files.update(str(p.relative_to(root))for p in(root/'verification/run16').rglob('*')if p.is_file())
manifest={p:hashlib.sha256((root/p).read_bytes()).hexdigest()for p in sorted(files)}
artifact=root/'artifacts/NS_P14_RUN16_COMPLETE_AUDIT_20261111.zip';artifact.parent.mkdir(exist_ok=True)
with zipfile.ZipFile(artifact,'w',zipfile.ZIP_DEFLATED,compresslevel=9)as z:
    for p in sorted(files):z.write(root/p,p)
    z.writestr('AUDIT_MANIFEST_SHA256.json',json.dumps(manifest,indent=2)+'\n')
    z.writestr('BASELINE.txt','Baseline: '+verified['baseline_commit']+'\nCheckout work and use the fixed toolchain/mathlib. This ZIP carries Run16 additions and evidence, not vendored dependencies.\n')
with zipfile.ZipFile(artifact)as z:
    assert z.testzip()is None
    expected=json.loads(z.read('AUDIT_MANIFEST_SHA256.json'))
    for p,h in expected.items():assert hashlib.sha256(z.read(p)).hexdigest()==h,p
sha=hashlib.sha256(artifact.read_bytes()).hexdigest();artifact.with_suffix('.zip.sha256').write_text(sha+'  '+artifact.name+'\n')
print(json.dumps(dict(path=str(artifact.relative_to(root)),sha256=sha,files=len(files),bytes=artifact.stat().st_size,crc='PASS'),indent=2))
