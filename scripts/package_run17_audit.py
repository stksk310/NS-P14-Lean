#!/usr/bin/env python3
"""Publish a reviewed Run17 snapshot to a fresh archive; never replace evidence."""
from pathlib import Path
import argparse,hashlib,json,os,re,subprocess,tempfile,zipfile
root=Path(__file__).resolve().parents[1]
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--output',default='artifacts/NS_P14_RUN17_COMPLETE_AUDIT_20261113.zip')
args=parser.parse_args();artifact_rel=Path(args.output)
if artifact_rel.is_absolute()or'..'in artifact_rel.parts or artifact_rel.parts[:1]!=('artifacts',)or artifact_rel.suffix!='.zip':
    parser.error('output must be a fresh repository-relative .zip under artifacts')
artifact=root/artifact_rel;sidecar=artifact.with_suffix('.zip.sha256')
if artifact.exists()or sidecar.exists():parser.error('archive or checksum already exists; publication is never overwritten')
def sha(data):return hashlib.sha256(data).hexdigest()
def relative_path(value):
    p=Path(value)
    assert not p.is_absolute()and'..'not in p.parts,('non-relative evidence path',value)
    return p
status=json.loads((root/'docs/RUN17_CLOSURE_STATUS.json').read_text())
assert status['status']=='COMPLETE'and status['run17_complete']and status['unproved_ids']==[]
verified_path=relative_path(status['verification']['evidence'])
assert verified_path.parts[:2]==('verification','run17')and verified_path.name=='verification.json'
evidence=root/verified_path.parent
verified=json.loads((root/verified_path).read_text())
assert verified['status']=='PASS_RUN17_PROOF_CLOSURE'and verified['fresh_new_production_cache']
review=json.loads((root/'verification/run17/final_review.json').read_text())
assert review['gate']=='PASS'and review['fresh_context']
assert all(review[k]==0 for k in ['critical','important','minor'])
head=review['head_commit'];assert re.fullmatch('[0-9a-f]{40}',head)
assert subprocess.check_output(['git','cat-file','-t',head],cwd=root).strip()==b'commit'
def reviewed_bytes(path):return subprocess.check_output(['git','show',head+':'+str(path)],cwd=root)
for name,key in [('SOURCE_SHA256.json','source_manifest_sha256'),('MANIFEST_SHA256.json','evidence_manifest_sha256')]:
    path=evidence/name;data=path.read_bytes()
    assert sha(data)==review[key],('review is for a different manifest',name)
    assert reviewed_bytes(path.relative_to(root))==data,('manifest absent from reviewed commit',name)
    for p,h in json.loads(data).items():
        rel=relative_path(p)
        assert sha((root/rel).read_bytes())==h,('current hash mismatch',p)
        assert sha(reviewed_bytes(rel))==h,('reviewed commit mismatch',p)
files=set(verified['sources']+verified['acceptance_tests']+verified['audit_sources']+[
    'NSP14.lean','README.md','LEAN_PROGRESS.md','docs/LEAN_PAPER_ALIGNMENT_JA.md',
    'lean-toolchain','lakefile.toml','lake-manifest.json','scripts/verify_run17.py',
    'scripts/check_run17_additive.py','scripts/package_run17_audit.py',
    'scripts/replay_run17_inherited.py','scripts/check_run17_publication.py',
    'NSP14/Additive/Kneser_SOURCE_LICENSE',
    'docs/superpowers/plans/2026-11-13-run17-kneser-savchev-chen-order.md'])
files.update(str(p.relative_to(root))for p in(root/'docs').glob('RUN17*')if p.is_file())
files.update(str(p.relative_to(root))for p in(root/'verification/run17').rglob('*')if p.is_file())
# This explicit boundary admits only publication state and the review report.
# Mathematical sources, evidence, and every other bundled document must match head.
publication_only={'docs/RUN17_CLOSURE_STATUS.json','docs/RUN17_EXECUTION_LEDGER_JA.md',
                  'docs/RUN17_FINAL_REVIEW_JA.md','verification/run17/final_review.json'}
for p in sorted(files-publication_only):
    assert reviewed_bytes(p)==(root/p).read_bytes(),('unreviewed packaged change',p)
ledger='docs/RUN17_EXECUTION_LEDGER_JA.md'
assert (root/ledger).read_bytes().startswith(reviewed_bytes(ledger)),('ledger must be append-only',ledger)
reviewed_status=json.loads(reviewed_bytes('docs/RUN17_CLOSURE_STATUS.json'))
mutable_status={'status','run17_complete','review','publication'}
assert {k:v for k,v in status.items()if k not in mutable_status}=={k:v for k,v in reviewed_status.items()if k not in mutable_status},'non-publication status changed'
review_doc=(root/'docs/RUN17_FINAL_REVIEW_JA.md').read_text()
assert head in review_doc and review['source_manifest_sha256']in review_doc,'review document does not identify the snapshot'
manifest={p:sha((root/p).read_bytes())for p in sorted(files)}
artifact.parent.mkdir(exist_ok=True)
with tempfile.TemporaryDirectory(prefix='.run17-package-',dir=artifact.parent)as tmp:
    candidate=Path(tmp)/'audit.zip'
    with zipfile.ZipFile(candidate,'x',zipfile.ZIP_DEFLATED,compresslevel=9)as z:
        for p in sorted(files):z.write(root/p,p)
        z.writestr('AUDIT_MANIFEST_SHA256.json',json.dumps(manifest,indent=2)+'\n')
        z.writestr('BASELINE.txt','Baseline: '+verified['baseline_commit']+'\nReviewed proof commit: '+head+'\nSelected verification: '+str(verified_path)+'\nUse the fixed toolchain/mathlib. Predecessors and earlier Run17 evidence are retained unchanged.\n')
    with zipfile.ZipFile(candidate)as z:
        assert z.testzip()is None
        assert len(z.namelist())==len(set(z.namelist()))==len(files)+2
        assert set(z.namelist())==files|{'AUDIT_MANIFEST_SHA256.json','BASELINE.txt'}
        assert json.loads(z.read('AUDIT_MANIFEST_SHA256.json'))==manifest
        for p,h in manifest.items():assert sha(z.read(p))==h,p
    digest=sha(candidate.read_bytes())
    checksum=Path(tmp)/'audit.sha256';checksum.write_text(digest+'  '+artifact.name+'\n')
    # Hard links publish validated complete files atomically and exclusively.
    os.link(candidate,artifact)
    os.link(checksum,sidecar)
assert sha(artifact.read_bytes())==digest
print(json.dumps(dict(path=str(artifact_rel),sha256=digest,files=len(files),entries=len(files)+2,
                     bytes=artifact.stat().st_size,crc='PASS',reviewed_commit=head),indent=2))
