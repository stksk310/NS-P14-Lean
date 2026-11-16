#!/usr/bin/env python3
"""Isolated regression of Run17 preservation and snapshot-binding guards."""
from pathlib import Path
import argparse,hashlib,json,shutil,subprocess,sys,tempfile
root=Path(__file__).resolve().parents[1]
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--full',action='store_true',help='also clone a committed snapshot and exercise positive packaging')
parser.add_argument('--head',help='actual reviewed candidate commit for --full')
args=parser.parse_args();cases=[]
def run(script,arguments,cwd):
    return subprocess.run([sys.executable,script,*arguments],cwd=cwd,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
def sha(data):return hashlib.sha256(data).hexdigest()
with tempfile.TemporaryDirectory(prefix='nsp14-run17-publication-')as tmp:
    isolated=Path(tmp)/'guards';(isolated/'scripts').mkdir(parents=True)
    for name in ['verify_run17.py','check_run17_additive.py','replay_run17_inherited.py','package_run17_audit.py']:
        shutil.copy2(root/'scripts'/name,isolated/'scripts'/name)
    existing=isolated/'verification/run17/existing';existing.mkdir(parents=True)
    sentinel=existing/'accepted.json';sentinel.write_bytes(b'accepted evidence\n')
    result=run('scripts/verify_run17.py',['--output-dir','verification/run17/existing'],isolated)
    assert result.returncode and 'already exists'in result.stdout and sentinel.read_bytes()==b'accepted evidence\n'
    cases.append('verifier refuses existing evidence directory before any replay')
    output=isolated/'existing.json';output.write_bytes(b'old numeric evidence\n')
    for name,arguments in [('check_run17_additive.py',[]),('replay_run17_inherited.py',['coordinates'])]:
        result=run('scripts/'+name,[*arguments,'--output','existing.json'],isolated)
        assert result.returncode and 'already exists'in result.stdout and output.read_bytes()==b'old numeric evidence\n'
        cases.append(name+' refuses existing numeric output')
    artifacts=isolated/'artifacts';artifacts.mkdir()
    for kind in ['archive','checksum']:
        p=artifacts/('sentinel.zip'if kind=='archive'else'sentinel.zip.sha256')
        p.write_bytes(b'published immutable bytes\n')
        result=run('scripts/package_run17_audit.py',['--output','artifacts/sentinel.zip'],isolated)
        assert result.returncode and 'already exists'in result.stdout and p.read_bytes()==b'published immutable bytes\n'
        cases.append('packager refuses existing '+kind)
        p.unlink()
    if args.full:
        assert args.head,'--full requires --head'
        head=subprocess.check_output(['git','rev-parse',args.head+'^{commit}'],cwd=root,text=True).strip()
        clone=Path(tmp)/'snapshot'
        subprocess.run(['git','clone','--shared','--no-hardlinks','--quiet',str(root),str(clone)],check=True)
        subprocess.run(['git','checkout','--quiet','--detach',head],cwd=clone,check=True)
        status_path=clone/'docs/RUN17_CLOSURE_STATUS.json';status=json.loads(status_path.read_text())
        selected=clone/Path(status['verification']['evidence']).parent
        # Synthetic attestations are confined to this temporary tooling test.
        # They exercise binding; they do not certify a real independent review.
        review={'gate':'PASS','fresh_context':True,'head_commit':head,'critical':0,'important':0,'minor':0,
                'source_manifest_sha256':sha((selected/'SOURCE_SHA256.json').read_bytes()),
                'evidence_manifest_sha256':sha((selected/'MANIFEST_SHA256.json').read_bytes()),'test_only':True}
        review_path=clone/'verification/run17/final_review.json'
        def set_review(value):review_path.write_text(json.dumps(value,indent=2)+'\n')
        set_review(review)
        status.update(status='COMPLETE',run17_complete=True,review='TEMPORARY TOOL TEST ONLY')
        status_path.write_text(json.dumps(status,ensure_ascii=False,indent=2)+'\n')
        (clone/'docs/RUN17_FINAL_REVIEW_JA.md').write_text('TEMPORARY TOOL TEST ONLY\n'+head+'\n'+review['source_manifest_sha256']+'\n')
        def package(name):return run('scripts/package_run17_audit.py',['--output','artifacts/'+name+'.zip'],clone)
        result=package('positive');assert result.returncode==0,result.stdout
        published=clone/'artifacts/positive.zip';published_sha=sha(published.read_bytes())
        cases.append('positive packaging of exact committed source/evidence succeeds in isolated clone')
        result=package('positive');assert result.returncode and sha(published.read_bytes())==published_sha
        cases.append('second positive invocation cannot overwrite published ZIP')
        for field,value in [('head_commit','0'*40),('source_manifest_sha256','0'*64),('evidence_manifest_sha256','0'*64)]:
            changed=dict(review);changed[field]=value;set_review(changed)
            result=package('invalid_'+field)
            assert result.returncode and not(clone/('artifacts/invalid_'+field+'.zip')).exists()
            cases.append('rejects invalid or stale '+field)
        changed=dict(review);changed['head_commit']=json.loads((selected/'verification.json').read_text())['baseline_commit'];set_review(changed)
        result=package('stale_valid_commit')
        assert result.returncode and not(clone/'artifacts/stale_valid_commit.zip').exists()
        cases.append('rejects a real but stale reviewed commit')
        set_review(review)
        doc=clone/'docs/RUN17_WORKING_NOTES.md';original=doc.read_bytes();doc.write_bytes(original+b'\nunreviewed change\n')
        result=package('changed_document');assert result.returncode and not(clone/'artifacts/changed_document.zip').exists()
        doc.write_bytes(original);cases.append('rejects unreviewed packaged document change')
        ledger=clone/'docs/RUN17_EXECUTION_LEDGER_JA.md';ledger.write_bytes(ledger.read_bytes()+b'\nPublication-only append for isolated test.\n')
        result=package('publication_append');assert result.returncode==0,result.stdout
        cases.append('explicit append-only publication ledger boundary succeeds')
print(json.dumps({'status':'PASS_ISOLATED_PUBLICATION_GUARDS','full':args.full,'cases':cases},indent=2))
