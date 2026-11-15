#!/usr/bin/env python3
"""Independent read-only audit of committed V06 validation evidence (stdlib only)."""
import argparse,gzip,hashlib,json,pathlib,re,subprocess
p=argparse.ArgumentParser();p.add_argument('--root',required=True);p.add_argument('--run',required=True);a=p.parse_args()
root=pathlib.Path(a.root);run=root/a.run
read=lambda p:json.loads(p.read_text())
sha=lambda b:hashlib.sha256(b).hexdigest()
git=lambda *args:subprocess.check_output(['git',*args],cwd=root)
base='a7504eea25f02728d1be6cd0082e8484d639dbe2'
proof='d446fc2f18f7a8603d1eedd446e93810dc44d01c'
s=read(run/'verification.json')
assert s['status']=='V06_ALIGNMENT_COMPLETE' and s['v06_alignment_complete'] is True
assert s['proof_snapshot_commit']==proof and s['baseline_commit']==base
assert s['scope']==['endpoint','antipodal_integer_payment','nonantipodal_integer_payment','higher_from_second','dense_two_branches']
assert s['not_claimed']==['N4','Run19','all_P14']
checks=s['checks'];assert len(checks)==289 and all(x['passed'] is True and x['exit_code']==0 for x in checks)
assert len({c['name'] for c in checks})==len(checks)
assert len(s['fixture_order'])==s['fixture_count']==273
assert sum(c['name'].startswith(('fixture_','v06_fixture_')) for c in checks)==273
source=read(run/'SOURCE_SHA256.json');evidence=read(run/'MANIFEST_SHA256.json')
assert len(source)==1497
for name,h in source.items():
 data=(root/name).read_bytes();assert sha(data)==h,name
 assert sha(git('show',proof+':'+name))==h,name
actual={str(x.relative_to(root)):sha(x.read_bytes()) for x in run.rglob('*') if x.is_file() and x.name!='MANIFEST_SHA256.json'}
assert actual==evidence
retained=read(run/'INHERITED_EVIDENCE_SHA256.json')
assert len(retained)==s['preserved_evidence_count']
for name,h in retained.items():assert sha((root/name).read_bytes())==h,name
policy=read(root/'docs/V06_ALIGNMENT_CHANGE_POLICY.json')
assert policy['base']==base
old={line.split('\t')[1]:line.split()[2] for line in git('ls-tree','-r',base).decode().splitlines()}
modified=set(policy['modified_files']);append=set(policy['append_only'])
for name,oid in old.items():
 data=(root/name).read_bytes()
 if name in append:assert data.startswith(git('show',base+':'+name)),name
 elif name not in modified:assert hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()==oid,name
r16='verification/run18/runs/release_candidate_20261115_r16'
prior=read(root/r16/'verification.json');mapping=read(run/'COMMAND_MAP.json')
assert len(mapping)==len(prior['checks'])==280
bycheck={c['name']:c for c in checks}
for before,m in zip(prior['checks'],mapping):
 expected=[x.replace(r16+'/',a.run+'/') for x in before['command']]
 assert m==dict(name=before['name'],old_command=before['command'],new_command=expected),before['name']
 assert bycheck[before['name']]['command']==expected,before['name']
assert set(prior['fixture_order'])<=set(s['fixture_order'])
rows=json.loads(gzip.decompress((run/'declarations.json.gz').read_bytes()))
objects=[json.loads(x) for x in gzip.decompress((run/'environment_axioms.log.gz').read_bytes()).decode().splitlines() if x.startswith('{')]
meta=[x for x in objects if x.get('audit_metadata') is True];assert len(meta)==1
raw=[x for x in objects if x.get('audit_metadata') is not True]
key=lambda rows:{x['name']:x for x in rows}
current=key(rows);rawkey=key(raw);assert len(rows)==len(current)==len(rawkey)==s['environment_declarations']
allowed={'propext','Classical.choice','Quot.sound'}
mods={x[:-5].replace('/','.') for x in modified|{'NSP14/Width/IntegerPayment.lean','NSP14/Width/HigherFromSecond.lean','tests/V06Endpoint.lean','tests/V06IntegerPayment.lean','tests/V06HigherFromSecond.lean','tests/V06Dense.lean'}}
assert len(mods)==17 and set(s['normal_explicit_type_and_axiom_coverage'])==mods
assert mods|{'NSP14','audit.v06_alignment.RouteChecks'}<=set(meta[0]['imported_modules'])
assert mods<={r['module'] for r in rows if 'type' in r and 'explicit_type' in r}
for name,r in current.items():
 assert set(r['axioms'])<=allowed and name not in r['axioms'],name
 for k in ['name','module','axioms','type','explicit_type']:assert r.get(k)==rawkey[name].get(k),(name,k)
 assert r['exported_kind']==rawkey[name]['kind']
 if r['module'] in mods:assert 'type' in r and 'explicit_type' in r,name
 assert sha((root/r['source']).read_bytes())==r['source_sha256'],name
baseline=json.loads(gzip.decompress((run/'base_declarations.json.gz').read_bytes()))
public=[r for r in baseline if not r['name'].startswith('_private.')]
for r in public:
 for field in ['type','explicit_type']:assert current[r['name']][field]==r[field],(r['name'],field)
coverage=read(run/'audit_coverage.json');assert coverage['base_public_exports_compared']==len(public)
assert s['fresh_whole_project_cache'] is True
fresh=read(run/'fresh_cache.json');assert fresh['whole_project_lib_and_ir'] and len(fresh['moved'])==2
assert fresh['shared_mathlib_cache_untouched'] is True
build=(run/'build.log').read_text();assert 'Build completed successfully' in build
built=set(re.findall(r'Built (NSP14(?:\.[\w]+)*) \(',build))
assert {n[:-5].replace('/','.') for n in modified|{'NSP14/Width/IntegerPayment.lean','NSP14/Width/HigherFromSecond.lean'}}<=built
routes=read(run/'routes.json');assert routes['status']=='PASS_V06_SOURCE_ROUTES' and len(routes['routes'])==13
assert all('NSP14.Endpoint.Stopping' not in v for v in routes['main_import_closures'].values())
assert 'NSP14.Endpoint.Stopping' in routes['finite_computational_closure']
controls=read(run/'alignment_controls.json');assert controls['status']=='PASS_V06_ALIGNMENT_NEGATIVE_CONTROLS'
assert controls['count']==24 and all(x['passed'] for x in controls['controls'])
assert sha((root/'audit/run18/RequestedGoals.lean').read_bytes())=='86a0a18eff0632cb915d67748dcef47a88991cebf287ef95750f58b450bea689'
print(json.dumps({'status':'PASS_INDEPENDENT_V06_EVIDENCE_CHECK','proof_commit':proof,'checks':len(checks),'fixtures':s['fixture_count'],'source_files':len(source),'manifested_evidence_files':len(evidence),'inherited_evidence_files':len(retained),'inherited_base_files':len(old),'declarations':len(rows),'typed_modules':len(mods),'unchanged_base_public_declarations':len(public),'cold_built_project_modules':len(built),'route_roots':len(routes['routes']),'negative_controls':24,'command_seconds':round(sum(c['seconds'] for c in checks),3)},indent=2))
