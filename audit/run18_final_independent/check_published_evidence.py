#!/usr/bin/env python3
"""Read-only independent check of the published Run18 COMPLETE snapshots."""
from pathlib import Path
import argparse,subprocess,json,hashlib,gzip,zipfile

p=argparse.ArgumentParser(description=__doc__)
p.add_argument('--root',type=Path,default=Path.cwd())
p.add_argument('--output',type=Path)
a=p.parse_args();R=a.root.resolve()
if a.output and a.output.exists():p.error('existing evidence is immutable')
HEAD='345e2d82fea50ef89e00a8f35c4fb53ac601d7ce'
BASE='c4fd8153f55bb231aab4168a47c1546888fa7ab0'
PROOF='a5f480c5136042597fceae23ad06d2ef3923ed02'
REVIEW='c97fa324d90277bcae20a88863366bff6ba7a35b'
V='verification/run18/runs/release_candidate_20261115_r16'
FULL=['W_SPARSE','W_FIVE','W_EDGE','X_BHP_EK','W_DENSE','W_CLOSE']
def git(*args):return subprocess.check_output(['git',*args],cwd=R)
def sha(b):return hashlib.sha256(b).hexdigest()
def blob(b):return hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
def tree(c):return {s.split('\t',1)[1]:s.split('\t',1)[0]for s in git('ls-tree','-r','--format=%(objectname)%x09%(path)',c).decode().splitlines()}
trees={c:tree(c)for c in [HEAD,BASE,PROOF,REVIEW]}
source=json.loads((R/V/'SOURCE_SHA256.json').read_text())
evidence=json.loads((R/V/'MANIFEST_SHA256.json').read_text())
assert len(source)==2033 and len(evidence)==297
for f,h in source.items():
    b=(R/f).read_bytes();assert sha(b)==h,f
    assert all(trees[c].get(f)==blob(b)for c in [HEAD,PROOF,REVIEW]),f
for f,h in evidence.items():
    b=(R/f).read_bytes();assert sha(b)==h,f
    assert all(trees[c].get(f)==blob(b)for c in [HEAD,REVIEW]),f
actual={str(q.relative_to(R))for q in(R/V).rglob('*')if q.is_file()and q.name!='MANIFEST_SHA256.json'}
assert actual==set(evidence)
summary=json.loads((R/V/'verification.json').read_text())
assert summary['status']=='PASS_RUN18_COMPLETE_VALIDATION'and summary['run18_complete']is True
assert len(summary['checks'])==280 and len(summary['fixture_order'])==268 and all(c['passed']for c in summary['checks'])
assert summary['closed_ids']==FULL and summary['unproved_ids']==[] and not summary['expected_open_acceptances']
decision_path='verification/run18/COMPLETE_publication_decision_20261115.json'
d=json.loads((R/decision_path).read_text())
assert d['verdict']=='PASS'and all(d[k]==0 for k in ['critical','important','minor'])
assert d['closed_ids']==FULL and d['run18_complete']is True and d['pending']==d['declined']==[]
assert d['source_snapshot_commit']==PROOF and d['reviewed_commit']==REVIEW
for key,f in [('verification_summary_sha256',V+'/verification.json'),('verification_manifest_sha256',V+'/MANIFEST_SHA256.json'),('review_report_sha256',d['review_report'])]:assert d[key]==sha((R/f).read_bytes())
status=json.loads((R/'docs/RUN18_CLOSURE_STATUS.json').read_text())
assert status['run18_complete']is True and status['closed_ids']==FULL and status['unproved_ids']==[]
assert status['verification']['verification_sha256']==sha((R/V/'verification.json').read_bytes())
assert status['verification']['source_manifest_sha256']==sha((R/V/'SOURCE_SHA256.json').read_bytes())
assert status['verification']['evidence_manifest_sha256']==sha((R/V/'MANIFEST_SHA256.json').read_bytes())
append={'NSP14.lean','LEAN_PROGRESS.md','docs/LEAN_PAPER_ALIGNMENT_JA.md'}
for f,h in trees[BASE].items():
    if f in append:assert(R/f).read_bytes().startswith(git('show',BASE+':'+f)),f
    else:assert blob((R/f).read_bytes())==h,f
prior=[f for f in trees[PROOF]if f.startswith(('verification/','artifacts/'))]
assert len(prior)==7212
for f in prior:assert blob((R/f).read_bytes())==trees[PROOF][f],f
requested='audit/run18/RequestedGoals.lean';frozen='86a0a18eff0632cb915d67748dcef47a88991cebf287ef95750f58b450bea689'
assert sha((R/requested).read_bytes())==frozen
first=git('log','--diff-filter=A','--format=%H',HEAD,'--',requested).decode().strip()
assert sha(git('show',first+':'+requested))==frozen
raw=[json.loads(s)for s in gzip.decompress((R/V/'environment_axioms.log.gz').read_bytes()).decode().splitlines()if s.startswith('{')]
processed=json.loads(gzip.decompress((R/V/'declarations.json.gz').read_bytes()))
assert len(raw)==len(processed)==10662
byname={x['name']:x for x in raw};assert len(byname)==len(raw)
allowed={'propext','Classical.choice','Quot.sound'}
for x in processed:
    assert set(x['axioms'])<=allowed and x['name']not in x['axioms'],x['name']
    assert sorted(x['axioms'])==sorted(byname[x['name']]['axioms']),x['name']
    assert x['source_sha256']==sha((R/x['source']).read_bytes()),x['name']
new=[x for x in processed if x['source']in summary['sources']]
assert len(new)==2421 and all(x.get('type')and x.get('explicit_type')for x in new)
exports=['NSP14.Lex.bhp_ek','NSP14.Run18.edge_closed','NSP14.Run18.dense_closed','NSP14.Run18.sparse_closed','NSP14.Run18.five_closed','NSP14.Run18.width_closed','NSP14.Run18.all_closed','NSP14.Lex.exists_lex_sameHilbert','NSP14.NumericalSemigroup.narrow_width_comparison']
assert set(exports)<=byname.keys()
archives=[]
for q in sorted((R/'artifacts').glob('*RUN18*.zip')):
    with zipfile.ZipFile(q)as z:
        names=z.namelist();assert len(names)==len(set(names))and z.testzip()is None
        m=json.loads(z.read('BUNDLE_SHA256.json'));assert set(names)==set(m)|{'BUNDLE_SHA256.json'}
        for f,h in m.items():assert sha(z.read(f))==h,(q.name,f)
        s=json.loads(z.read('docs/RUN18_CLOSURE_STATUS.json'))
        if 'COMPLETE'in q.name:
            assert len(names)==2338 and s['run18_complete']is True and s['closed_ids']==FULL and s['unproved_ids']==[]
            for f,h in {**source,**evidence}.items():assert m[f]==h,f
            for f in m:assert z.read(f)==(R/f).read_bytes(),f
            assert json.loads(z.read(decision_path))==d
            assert m[d['review_report']]==d['review_report_sha256']
        else:assert s['run18_complete']is False
        archives.append(dict(path=str(q.relative_to(R)),entries=len(names),sha256=sha(q.read_bytes()),complete=s['run18_complete']))
receipt=json.loads((R/'verification/run18/complete_publication_receipt_20261115.json').read_text())
bundle=receipt['package_result'];assert sha((R/bundle['archive']).read_bytes())==bundle['archive_sha256']
assert bundle['entries']==2338 and bundle['crc']=='PASS'
# Exercise the real existing-output rejection; it must happen before gate work or any write.
archive=R/bundle['archive'];before=archive.read_bytes()
check=subprocess.run(['python3','scripts/package_run18_audit.py','--verification',V,'--review',decision_path,'--output',bundle['archive']],cwd=R,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
assert check.returncode==2 and 'archive already exists'in check.stdout and archive.read_bytes()==before
result=dict(status='PASS_INDEPENDENT_COMPLETE_PUBLISHED_EVIDENCE',audited_commit=HEAD,proof_commit=PROOF,reviewed_commit=REVIEW,source_entries=len(source),evidence_entries=len(evidence),baseline_files=len(trees[BASE]),prior_evidence_preserved=len(prior),raw_declarations=len(raw),new_declarations=len(new),frozen_requested_goals_sha256=frozen,first_contract_commit=first,original_complete_archive_overwrite_rejected=True,exports={n:byname[n]for n in exports},archives=archives)
if a.output:
    a.output.parent.mkdir(parents=True,exist_ok=True)
    with a.output.open('x')as f:f.write(json.dumps(result,ensure_ascii=False,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items()if k!='exports'},indent=2))
