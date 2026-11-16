#!/usr/bin/env python3
"""Immutable audit bundle with actual proof/evidence/review Git-byte binding.

This is a review bundle, not a complete offline mathlib/toolchain checkout.
"""
from pathlib import Path
import argparse, hashlib, importlib.util, json, subprocess, zipfile
ROOT=Path(__file__).resolve().parents[1]
spec=importlib.util.spec_from_file_location('run19_verify',ROOT/'scripts/verify_run19.py')
verify=importlib.util.module_from_spec(spec);spec.loader.exec_module(verify)
sha=verify.sha;safe=verify.safe;git=verify.git

def checked_payload(root,evidence,review):
    out=safe(root,evidence);review_path=safe(root,review)
    summary=json.loads((out/'verification.json').read_text());manifest=json.loads((out/'MANIFEST_SHA256.json').read_text())
    if summary['status']!='PASS_RUN19_COMPLETE_VALIDATION' or summary['unproved_ids'] or set(summary['closed_ids'])!=verify.FULL_IDS:
        raise ValueError('closure scope differs')
    if not summary['fresh_whole_project_cache'] or any(not r['passed'] for r in summary['checks']):raise ValueError('fresh validation required')
    verify.check_evidence_manifest(root,out,manifest)
    source=json.loads((out/'SOURCE_SHA256.json').read_text());proof=summary['proof_snapshot_commit']
    verify.check_source_manifest(root,source,proof)
    r=json.loads(review_path.read_text())
    if r.get('verdict')!='PASS' or any(r.get(k)!=0 for k in ['critical','important','minor']) or r.get('pending')!=[] or r.get('declined')!=[]:
        raise ValueError('review gate failed')
    if set(r.get('closed_ids',[]))!=verify.FULL_IDS or r.get('source_snapshot_commit')!=proof:raise ValueError('review snapshot/scope mismatch')
    if r.get('verification_summary_sha256')!=sha((out/'verification.json').read_bytes()) or r.get('verification_manifest_sha256')!=sha((out/'MANIFEST_SHA256.json').read_bytes()):raise ValueError('review evidence mismatch')
    report=safe(root,r['review_report'])
    if sha(report.read_bytes())!=r['review_report_sha256']:raise ValueError('review body mismatch')
    reviewed=r['reviewed_commit'];head=git(root,'rev-parse','HEAD').decode().strip()
    subprocess.run(['git','merge-base','--is-ancestor',reviewed,head],cwd=root,check=True)
    # Every evidence entry is in the exact reviewed commit, including manifest.
    for name in list(manifest)+[str((out/'MANIFEST_SHA256.json').relative_to(root))]:
        if git(root,'show',reviewed+':'+name)!=safe(root,name).read_bytes():raise ValueError('reviewed evidence Git bytes mismatch')
    for name in [review,str(report.relative_to(root))]:
        if git(root,'show',head+':'+name)!=safe(root,name).read_bytes():raise ValueError('review Git bytes mismatch')
    payload={n:safe(root,n).read_bytes() for n in source}
    for n in manifest:payload[n]=safe(root,n).read_bytes()
    payload[str((out/'MANIFEST_SHA256.json').relative_to(root))]=(out/'MANIFEST_SHA256.json').read_bytes()
    for n in [review,str(report.relative_to(root))]:payload[n]=safe(root,n).read_bytes()
    # Initial RED/frozen contracts, port provenance and prior V06 receipts are part of the bundle.
    for p in (root/'verification/run19/sources').rglob('*'):
        if p.is_file() and '__pycache__' not in p.parts and p.suffix!='.pyc':
            payload[str(p.relative_to(root))]=p.read_bytes()
    binding={'proof_snapshot_commit':proof,'reviewed_evidence_commit':reviewed,'review_commit':head,
      'evidence':evidence,'review':review,'review_report':r['review_report'],'complete_offline_checkout':False,
      'scope':'Run19 ten contracts; Run20 whole-P14 composition remains'}
    payload['RUN19_BINDING.json']=(json.dumps(binding,indent=2)+'\n').encode()
    return payload,binding

def package(root,evidence,review,archive):
    dest=safe(root,archive)
    if not archive.startswith('artifacts/NS_P14_LEAN_RUN19_') or not archive.endswith('.zip'):raise ValueError('new Run19 archive name required')
    if dest.exists():raise ValueError('archive already exists')
    payload,binding=checked_payload(root,evidence,review)
    manifest={n:sha(b) for n,b in payload.items()};payload['BUNDLE_SHA256.json']=(json.dumps(manifest,indent=2)+'\n').encode()
    with dest.open('xb') as stream:
        with zipfile.ZipFile(stream,'w',compression=zipfile.ZIP_DEFLATED) as z:
            for n,b in sorted(payload.items()):z.writestr(n,b)
    with zipfile.ZipFile(dest) as z:
        if z.testzip() is not None:raise ValueError('ZIP CRC failed')
        if set(z.namelist())!=set(payload) or any(sha(z.read(n))!=manifest[n] for n in manifest):raise ValueError('ZIP payload hash/fileset mismatch')
    return {'archive':archive,'sha256':sha(dest.read_bytes()),'entries':len(payload),'CRC_and_all_payload_hashes':True,**binding}

def main():
    p=argparse.ArgumentParser();p.add_argument('--evidence',required=True);p.add_argument('--review',required=True);p.add_argument('--archive',required=True);a=p.parse_args()
    try:print(json.dumps(package(ROOT,a.evidence,a.review,a.archive),indent=2))
    except (ValueError,OSError,subprocess.CalledProcessError) as e:p.exit(1,str(e)+'\n')
if __name__=='__main__':main()
