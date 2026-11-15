from pathlib import Path
import argparse,subprocess,hashlib,json,zipfile,gzip
parser=argparse.ArgumentParser(description='Read-only independent audit of published Run18 evidence')
parser.add_argument('--output',help='fresh JSON file; default prints only')
args=parser.parse_args()
output=Path(args.output)if args.output else None
if output is not None and output.exists():parser.error('existing audit evidence must not be overwritten')
R=Path(__file__).resolve().parents[2]
HEAD='58a0f54651916a4f7d6aa2e172d9250d91fd25f4'
BASE='c4fd8153f55bb231aab4168a47c1546888fa7ab0'
PROOF='bc554ffc0231c0e83fdf4c62673e438cc123c417'
REVIEW='b22600b61e013da0e3d55e5a6b0559216cc4d76f'
v='verification/run18/runs/release_candidate_20261114_r05'
def git(*a):return subprocess.check_output(['git',*a],cwd=R)
def sha(b):return hashlib.sha256(b).hexdigest()
def blob(b):return hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
def tree(c):return dict((line.split('\t',1)[1],line.split('\t',1)[0])for line in git('ls-tree','-r','--format=%(objectname)%x09%(path)',c).decode().splitlines())
trees={c:tree(c)for c in [HEAD,BASE,PROOF,REVIEW]}
source=json.loads((R/v/'SOURCE_SHA256.json').read_text())
evidence=json.loads((R/v/'MANIFEST_SHA256.json').read_text())
for f,h in source.items():
    b=(R/f).read_bytes();assert sha(b)==h,f
    assert all(trees[c].get(f)==blob(b)for c in [HEAD,PROOF,REVIEW]),f
for f,h in evidence.items():
    b=(R/f).read_bytes();assert sha(b)==h,f
    assert all(trees[c].get(f)==blob(b)for c in [HEAD,REVIEW]),f
actual={str(p.relative_to(R))for p in(R/v).rglob('*')if p.is_file()and p.name!='MANIFEST_SHA256.json'}
assert actual==set(evidence)
summary=json.loads((R/v/'verification.json').read_text());assert len(summary['checks'])==183 and all(c['passed']for c in summary['checks'])
review=json.loads((R/'verification/run18/review_snapshot_five_20261114.json').read_text())
for key,path in [('verification_summary_sha256',v+'/verification.json'),('verification_manifest_sha256',v+'/MANIFEST_SHA256.json'),('review_report_sha256',review['review_report'])]:assert review[key]==sha((R/path).read_bytes())
assert review['reviewed_commit']==REVIEW and review['source_snapshot_commit']==PROOF
append={'NSP14.lean','LEAN_PROGRESS.md','docs/LEAN_PAPER_ALIGNMENT_JA.md'}
for f,h in trees[BASE].items():
    if f in append:assert(R/f).read_bytes().startswith(git('show',BASE+':'+f)),f
    else:assert blob((R/f).read_bytes())==h,f
original_evidence=[f for f in trees[PROOF]if f.startswith(('verification/','artifacts/'))]
assert len(original_evidence)==3653
for f in original_evidence:assert blob((R/f).read_bytes())==trees[PROOF][f],f
requested='audit/run18/RequestedGoals.lean';expected='86a0a18eff0632cb915d67748dcef47a88991cebf287ef95750f58b450bea689'
assert sha((R/requested).read_bytes())==expected
first=git('log','--diff-filter=A','--format=%H','--',requested).decode().strip();assert sha(git('show',first+':'+requested))==expected
raw=[json.loads(l)for l in gzip.decompress((R/v/'environment_axioms.log.gz').read_bytes()).decode().splitlines()if l.startswith('{')]
decs=json.loads(gzip.decompress((R/v/'declarations.json.gz').read_bytes()))
assert len(raw)==len(decs)==8942
assert len({d['name']for d in raw})==len(raw)
allowed={'propext','Classical.choice','Quot.sound'}
byname={d['name']:d for d in raw}
for d in decs:
    assert set(d['axioms'])<=allowed and d['name']not in d['axioms'],d['name']
    assert sorted(d['axioms'])==sorted(byname[d['name']]['axioms'])
    assert d['source_sha256']==sha((R/d['source']).read_bytes())
news=[d for d in decs if d['source']in summary['sources']]
assert len(news)==701 and all(d.get('type')and d.get('explicit_type')for d in news)
assert {'NSP14.Run18.sparse_closed','NSP14.Run18.five_closed'}<=set(byname)
assert not {'NSP14.Lex.bhp_ek','NSP14.Run18.edge_closed','NSP14.Run18.dense_closed','NSP14.Run18.width_closed'}&set(byname)
status=json.loads((R/'docs/RUN18_CLOSURE_STATUS.json').read_text());assert status['status']=='PARTIAL'and status['run18_complete']is False
assert status['closed_ids']==['W_SPARSE','W_FIVE'] and set(status['unproved_ids'])=={'X_BHP_EK','W_EDGE','W_DENSE','W_CLOSE'}
archives=[]
for p in sorted((R/'artifacts').glob('*RUN18*.zip')):
    with zipfile.ZipFile(p)as z:
        names=z.namelist();assert len(names)==len(set(names))and z.testzip()is None
        m=json.loads(z.read('BUNDLE_SHA256.json'));assert set(names)==set(m)|{'BUNDLE_SHA256.json'}
        for f,h in m.items():assert sha(z.read(f))==h,(p.name,f)
        s=json.loads(z.read('docs/RUN18_CLOSURE_STATUS.json'));assert s['run18_complete']is False
        if 'FIVE_CLOSURE'in p.name:
            assert s['closed_ids']==['W_SPARSE','W_FIVE']
            for f,h in {**source,**evidence}.items():assert m.get(f)==h,f
            assert m[review['review_report']]==review['review_report_sha256']
            assert json.loads(z.read('verification/run18/review_snapshot_five_20261114.json'))==review
        archives.append(dict(path=str(p.relative_to(R)),entries=len(names),sha256=sha(p.read_bytes()),closed_ids=s['closed_ids']))
result=dict(status='PASS_INDEPENDENT_PUBLISHED_EVIDENCE_CHECK',head=HEAD,source_manifest=len(source),evidence_manifest=len(evidence),frozen_baseline_files=len(trees[BASE]),preserved_before_R05=len(original_evidence),raw_declarations=len(raw),new_declarations=len(news),requested_goals_sha256=expected,first_contract_commit=first,archives=archives)
if output is not None:
    output.parent.mkdir(parents=True,exist_ok=True)
    with output.open('x')as f:f.write(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
