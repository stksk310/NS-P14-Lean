#!/usr/bin/env python3
"""Regression tests for publication binding and immutable output paths, in isolated temporary repos."""
from pathlib import Path
import hashlib,importlib.util,json,subprocess,tempfile
ROOT=Path(__file__).resolve().parents[1]
spec=importlib.util.spec_from_file_location('run18_package',ROOT/'scripts/package_run18_audit.py')
pkg=importlib.util.module_from_spec(spec);spec.loader.exec_module(pkg)
def main():
    count=0
    with tempfile.TemporaryDirectory(prefix='run18-guards-')as tmp:
        r=Path(tmp);v=r/'verification/run18/runs/guard';v.mkdir(parents=True)
        def write(f,data):
            p=r/f;p.parent.mkdir(parents=True,exist_ok=True);p.write_text(data)
        def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
        def git(*args):return subprocess.check_output(['git',*args],cwd=r,stderr=subprocess.STDOUT).decode().strip()
        git('init','-q');write('src.lean','-- guard fixture, not a mathematical verification\n')
        git('add','src.lean');git('-c','user.name=Run18 Guard','-c','user.email=guard@example.invalid','commit','-qm','source')
        base=git('rev-parse','HEAD')
        summary=dict(status='PASS_RUN18_PARTIAL_VALIDATION',run18_complete=False,fresh_project_test_cache=True,fresh_new_production_cache=True,checks=[dict(passed=True)],proof_snapshot_commit=base,closed_ids=['W_SPARSE','W_FIVE','W_EDGE'],unproved_ids=['X_BHP_EK','W_DENSE','W_CLOSE'])
        write('verification/run18/runs/guard/verification.json',json.dumps(summary))
        write('verification/run18/runs/guard/SOURCE_SHA256.json',json.dumps({'src.lean':sha(r/'src.lean')}))
        manifest={str(p.relative_to(r)):sha(p)for p in v.iterdir()}
        write('verification/run18/runs/guard/MANIFEST_SHA256.json',json.dumps(manifest))
        git('add','verification');git('-c','user.name=Run18 Guard','-c','user.email=guard@example.invalid','commit','-qm','evidence')
        head=git('rev-parse','HEAD')
        write('review.md','Isolated guard review fixture, not a mathematical review.\n')
        review=dict(review_report='review.md',review_report_sha256=sha(r/'review.md'),verdict='PASS',critical=0,important=0,source_snapshot_commit=base,reviewed_commit=head,
            verification_summary_sha256=sha(v/'verification.json'),verification_manifest_sha256=sha(v/'MANIFEST_SHA256.json'))
        write('review.json',json.dumps(review))
        pkg.checked_payload(r,'verification/run18/runs/guard','review.json');count+=1
        def fails(fragment):
            nonlocal count
            try:pkg.checked_payload(r,'verification/run18/runs/guard','review.json')
            except ValueError as e:assert fragment in str(e),(fragment,e);count+=1
            else:raise AssertionError('guard did not reject '+fragment)
        summary_original=(v/'verification.json').read_bytes()
        summary['closed_ids'].append('W_CLOSE');write('verification/run18/runs/guard/verification.json',json.dumps(summary));fails('closure scope differs');summary['closed_ids'].pop();(v/'verification.json').write_bytes(summary_original)
        summary['fresh_project_test_cache']=False;write('verification/run18/runs/guard/verification.json',json.dumps(summary));fails('cold validation required');(v/'verification.json').write_bytes(summary_original)
        write('verification/run18/runs/guard/unmanifested.log','unreviewed')
        fails('evidence coverage differs');(v/'unmanifested.log').unlink()
        original=(r/'src.lean').read_bytes();(r/'src.lean').write_text('changed\n');fails('source changed');(r/'src.lean').write_bytes(original)
        review['source_snapshot_commit']='0'*40;write('review.json',json.dumps(review));fails('review snapshot mismatch');review['source_snapshot_commit']=base
        review['important']=1;write('review.json',json.dumps(review));fails('review gate failed');review['important']=0;write('review.json',json.dumps(review))
        data=(v/'SOURCE_SHA256.json').read_bytes();(v/'SOURCE_SHA256.json').write_text('{}');fails('evidence changed');(v/'SOURCE_SHA256.json').write_bytes(data)
        for bad in ['../outside','/tmp/outside','src\\bad']:
            try:pkg.safe(r,bad)
            except ValueError:count+=1
            else:raise AssertionError('unsafe path accepted')
    for args,marker in [(['--output-dir','verification/run17/final'],'new directory'),(['--output-dir','verification/run18/runs/../bad'],'new directory'),(['--output-dir','/tmp/run18-test'],'new directory')]:
        r=subprocess.run(['python3','scripts/verify_run18.py',*args],cwd=ROOT,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
        assert r.returncode==2 and marker in r.stdout,r.stdout;count+=1
    with tempfile.TemporaryDirectory(prefix='guard_existing_',dir=ROOT/'verification/run18/runs')as tmp:
        marker=Path(tmp)/'sentinel';marker.write_text('retained')
        rel=str(Path(tmp).relative_to(ROOT))
        r=subprocess.run(['python3','scripts/verify_run18.py','--output-dir',rel],cwd=ROOT,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
        assert r.returncode==2 and 'output exists'in r.stdout and marker.read_text()=='retained'
        count+=1
    print('PASS_RUN18_PUBLICATION_GUARDS',count)
if __name__=='__main__':main()
