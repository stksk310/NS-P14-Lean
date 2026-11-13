#!/usr/bin/env python3
"""Publish a hash-bound Run17 bundle after proof, cold verification and review."""
from pathlib import Path
import hashlib,json,zipfile
root=Path(__file__).resolve().parents[1]
status=json.loads((root/'docs/RUN17_CLOSURE_STATUS.json').read_text())
assert status['status']=='COMPLETE'and status['run17_complete']and status['unproved_ids']==[]
verified=json.loads((root/'verification/run17/final/verification.json').read_text())
assert verified['status']=='PASS_RUN17_PROOF_CLOSURE'and verified['fresh_new_production_cache']
review=json.loads((root/'verification/run17/final_review.json').read_text())
assert review['gate']=='PASS'and review['fresh_context']
for name in ['SOURCE_SHA256.json','MANIFEST_SHA256.json']:
    for p,h in json.loads((root/'verification/run17/final'/name).read_text()).items():
        assert hashlib.sha256((root/p).read_bytes()).hexdigest()==h,('hash mismatch',p)
files=set(verified['sources']+verified['acceptance_tests']+verified['audit_sources']+[
    'NSP14.lean','README.md','LEAN_PROGRESS.md','docs/LEAN_PAPER_ALIGNMENT_JA.md',
    'lean-toolchain','lakefile.toml','lake-manifest.json','scripts/verify_run17.py',
    'scripts/check_run17_additive.py','scripts/package_run17_audit.py',
    'scripts/replay_run17_inherited.py',
    'NSP14/Additive/Kneser_SOURCE_LICENSE',
    'docs/superpowers/plans/2026-11-13-run17-kneser-savchev-chen-order.md'])
files.update(str(p.relative_to(root))for p in(root/'docs').glob('RUN17*')if p.is_file())
files.update(str(p.relative_to(root))for p in(root/'verification/run17').rglob('*')if p.is_file())
manifest={p:hashlib.sha256((root/p).read_bytes()).hexdigest()for p in sorted(files)}
artifact=root/'artifacts/NS_P14_RUN17_COMPLETE_AUDIT_20261113.zip'
artifact.parent.mkdir(exist_ok=True)
with zipfile.ZipFile(artifact,'w',zipfile.ZIP_DEFLATED,compresslevel=9)as z:
    for p in sorted(files):z.write(root/p,p)
    z.writestr('AUDIT_MANIFEST_SHA256.json',json.dumps(manifest,indent=2)+'\n')
    z.writestr('BASELINE.txt','Baseline: '+verified['baseline_commit']+'\nReviewed proof commit: '+review['head_commit']+'\nUse the fixed repository toolchain/mathlib. This archive contains Run17 additions and evidence; predecessors remain frozen at the baseline.\n')
with zipfile.ZipFile(artifact)as z:
    assert z.testzip()is None
    assert len(z.namelist())==len(set(z.namelist()))==len(files)+2
    assert set(z.namelist())==files|{'AUDIT_MANIFEST_SHA256.json','BASELINE.txt'}
    expected=json.loads(z.read('AUDIT_MANIFEST_SHA256.json'))
    assert expected==manifest
    for p,h in expected.items():assert hashlib.sha256(z.read(p)).hexdigest()==h,p
sha=hashlib.sha256(artifact.read_bytes()).hexdigest()
artifact.with_suffix('.zip.sha256').write_text(sha+'  '+artifact.name+'\n')
print(json.dumps(dict(path=str(artifact.relative_to(root)),sha256=sha,files=len(files),
                     entries=len(files)+2,bytes=artifact.stat().st_size,crc='PASS'),indent=2))
