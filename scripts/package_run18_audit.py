#!/usr/bin/env python3
"""Publish only a reviewed, immutable Run18 bundle with exactly the validated closure scope."""
from pathlib import Path
import argparse,hashlib,json,subprocess,zipfile
ROOT=Path(__file__).resolve().parents[1]
FULL_IDS=['W_SPARSE','W_FIVE','W_EDGE','X_BHP_EK','W_DENSE','W_CLOSE']
def sha(data):return hashlib.sha256(data).hexdigest()
def git(root,*args):return subprocess.check_output(['git',*args],cwd=root)
def safe(root,name):
    p=Path(name)
    if p.is_absolute()or'..'in p.parts or'\\'in name:raise ValueError('unsafe archive/source path')
    result=root/p
    if not result.resolve().is_relative_to(root.resolve()):raise ValueError('source escapes repository')
    return result

def checked_payload(root,verification,review):
    vdir=safe(root,verification)
    summary=json.loads((vdir/'verification.json').read_text())
    decision=json.loads(safe(root,review).read_text())
    complete=summary.get('run18_complete')is True
    expected='PASS_RUN18_COMPLETE_VALIDATION'if complete else'PASS_RUN18_PARTIAL_VALIDATION'
    if summary.get('status')!=expected or summary.get('run18_complete')is not complete:raise ValueError('not a validated snapshot')
    if summary.get('fresh_project_test_cache')is not True or summary.get('fresh_new_production_cache')is not True:raise ValueError('cold validation required')
    if not summary.get('checks')or not all(c.get('passed')is True for c in summary['checks']):raise ValueError('validation checks failed')
    scopes=[(['W_SPARSE','W_FIVE','W_EDGE'],{'X_BHP_EK','W_DENSE','W_CLOSE'}),
            (['W_SPARSE','W_FIVE','W_EDGE','X_BHP_EK'],{'W_DENSE','W_CLOSE'})]
    scope_ok=(summary.get('closed_ids')==FULL_IDS and summary.get('unproved_ids')==[])if complete else any(summary.get('closed_ids')==closed and set(summary.get('unproved_ids',[]))==remaining for closed,remaining in scopes)
    if not scope_ok:raise ValueError('closure scope differs')
    if complete and(decision.get('minor')!=0 or decision.get('closed_ids')!=FULL_IDS or decision.get('run18_complete')is not True or decision.get('pending')!=[]or decision.get('declined')!=[]):raise ValueError('complete review scope mismatch')
    if decision.get('verdict')!='PASS'or decision.get('critical')!=0 or decision.get('important')!=0:raise ValueError('review gate failed')
    if decision.get('source_snapshot_commit')!=summary['proof_snapshot_commit']:raise ValueError('review snapshot mismatch')
    if decision.get('verification_summary_sha256')!=sha((vdir/'verification.json').read_bytes()):raise ValueError('review summary mismatch')
    if decision.get('verification_manifest_sha256')!=sha((vdir/'MANIFEST_SHA256.json').read_bytes()):raise ValueError('review evidence mismatch')
    if decision.get('review_report_sha256')!=sha(safe(root,decision['review_report']).read_bytes()):raise ValueError('review report changed')
    source=json.loads((vdir/'SOURCE_SHA256.json').read_text());evidence=json.loads((vdir/'MANIFEST_SHA256.json').read_text())
    if set(source)&set(evidence):raise ValueError('source/evidence path collision')
    actual_evidence={str(p.relative_to(root))for p in vdir.rglob('*')if p.is_file()and p.name!='MANIFEST_SHA256.json'}
    if set(evidence)!=actual_evidence:raise ValueError('evidence coverage differs')
    payload={}
    for f,h in source.items():
        data=safe(root,f).read_bytes()
        if sha(data)!=h:raise ValueError('source changed: '+f)
        if sha(git(root,'show',summary['proof_snapshot_commit']+':'+f))!=h:raise ValueError('source snapshot bytes differ: '+f)
        if sha(git(root,'show',decision['reviewed_commit']+':'+f))!=h:raise ValueError('reviewed source bytes differ: '+f)
        payload[f]=data
    for f,h in evidence.items():
        data=safe(root,f).read_bytes()
        if sha(data)!=h:raise ValueError('evidence changed: '+f)
        if sha(git(root,'show',decision['reviewed_commit']+':'+f))!=h:raise ValueError('reviewed evidence bytes differ: '+f)
        payload[f]=data
    manifest_path=str(Path(verification)/'MANIFEST_SHA256.json')
    payload[manifest_path]=(vdir/'MANIFEST_SHA256.json').read_bytes()
    payload[review]=safe(root,review).read_bytes()
    return payload,summary,decision

def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--verification',required=True);p.add_argument('--review',required=True);p.add_argument('--output',required=True);a=p.parse_args()
    target=safe(ROOT,a.output)
    if Path(a.output).parts[:1]!=('artifacts',)or target.suffix!='.zip':p.error('a ZIP archive under artifacts is required')
    if target.exists():p.error('archive already exists')
    try:payload,summary,decision=checked_payload(ROOT,a.verification,a.review)
    except(ValueError,KeyError,FileNotFoundError,subprocess.CalledProcessError)as e:p.error(str(e))
    tag='COMPLETE'if summary['run18_complete']else'PARTIAL'
    other='PARTIAL'if summary['run18_complete']else'COMPLETE'
    if tag not in target.name or other in target.name:p.error('archive label differs from validated scope')
    extra=['docs/RUN18_CLOSURE_STATUS.json','docs/RUN18_EXECUTION_LEDGER_JA.md','docs/RUN18_FINAL_REVIEW_JA.md',
           'NSP14/Additive/Kneser_SOURCE_LICENSE','verification/run17/sources/provenance.json']
    for f in extra:
        payload[f]=safe(ROOT,f).read_bytes()
        if f!=decision['review_report']and payload[f]!=git(ROOT,'show',decision['reviewed_commit']+':'+f):p.error('unreviewed extra payload: '+f)
    status=json.loads(payload['docs/RUN18_CLOSURE_STATUS.json'])
    if status['run18_complete']is not summary['run18_complete']or status['closed_ids']!=summary['closed_ids']or status['unproved_ids']!=summary['unproved_ids']:p.error('status document overstates closure')
    manifest={f:sha(data)for f,data in sorted(payload.items())}
    payload['BUNDLE_SHA256.json']=(json.dumps(manifest,indent=2)+'\n').encode()
    target.parent.mkdir(parents=True,exist_ok=True)
    with zipfile.ZipFile(target,'x',compression=zipfile.ZIP_DEFLATED)as z:
        for f,data in sorted(payload.items()):z.writestr(f,data)
    with zipfile.ZipFile(target)as z:
        assert z.testzip()is None
        assert len(z.namelist())==len(set(z.namelist()))==len(payload)
        assert {f:sha(z.read(f))for f in manifest}==manifest
    print(json.dumps(dict(status='PUBLISHED_COMPLETE_BUNDLE'if summary['run18_complete']else'PUBLISHED_PARTIAL_BUNDLE',archive=a.output,archive_sha256=sha(target.read_bytes()),entries=len(payload),crc='PASS',run18_complete=summary['run18_complete']),indent=2))
if __name__=='__main__':main()
