from pathlib import Path
import json,gzip,hashlib,subprocess,re,importlib.util
ROOT=Path('/tmp/ns-p14-v06-alignment-20261116');RUN='verification/run18/runs/v06_alignment_20261115T152000Z_r01';V=ROOT/RUN
BASE='a7504eea25f02728d1be6cd0082e8484d639dbe2';PROOF='d446fc2f18f7a8603d1eedd446e93810dc44d01c';EVID='0880f6f30836873036b4d9908b7dcef50125d2c8';R16='verification/run18/runs/release_candidate_20261115_r16'
def git(*args):return subprocess.check_output(['git',*args],cwd=ROOT)
def sha(b):return hashlib.sha256(b).hexdigest()
def oid(b):return hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
def load(p):return json.loads((ROOT/p).read_text())
def tree(commit):
 out={}
 for row in git('ls-tree','-rz','--full-tree',commit).split(b'\0'):
  if row:
   meta,name=row.split(b'\t',1);mode,kind,h=meta.split();assert kind==b'blob';out[name.decode()]=(mode.decode(),h.decode())
 return out
assert git('rev-parse','HEAD').decode().strip()==EVID
bt,pt,et=tree(BASE),tree(PROOF),tree(EVID)
subprocess.run(['git','merge-base','--is-ancestor',PROOF,EVID],cwd=ROOT,check=True)
policy=load('docs/V06_ALIGNMENT_CHANGE_POLICY.json');assert policy['base']==BASE
source=load(RUN+'/SOURCE_SHA256.json');manifest=load(RUN+'/MANIFEST_SHA256.json');retained=load(RUN+'/INHERITED_EVIDENCE_SHA256.json')
assert set(source)=={n for n in et if n.split('/')[0] not in {'verification','artifacts'}}
for name,digest in source.items():
 p=ROOT/name;assert not any(x.is_symlink() for x in [p,*p.parents] if x.is_relative_to(ROOT));data=p.read_bytes();assert sha(data)==digest;assert oid(data)==pt[name][1]==et[name][1]
actual={str(p.relative_to(ROOT)) for p in V.rglob('*') if p.is_file() and p.name!='MANIFEST_SHA256.json'}
assert actual==set(manifest)
for name,digest in manifest.items():
 p=ROOT/name;assert not p.is_symlink();data=p.read_bytes();assert sha(data)==digest;assert oid(data)==et[name][1]
assert oid((V/'MANIFEST_SHA256.json').read_bytes())==et[RUN+'/MANIFEST_SHA256.json'][1]
actualold={name for name in et if name.split('/')[0] in {'verification','artifacts'} and not name.startswith(RUN+'/')}
assert actualold==set(retained)
for name,digest in retained.items():
 data=(ROOT/name).read_bytes();assert sha(data)==digest;assert oid(data)==pt[name][1]==et[name][1]
allowed=set(policy['modified_files']);app=set(policy['append_only']);assert set(bt)<=set(et)
for name,(_,h) in bt.items():
 data=(ROOT/name).read_bytes()
 if name in app:assert data.startswith(git('show',BASE+':'+name))
 elif name not in allowed:assert oid(data)==h==et[name][1]
new=set(et)-set(bt)
for name in new-set(policy['new_files']):assert re.fullmatch(r'verification/run18/runs/v06_alignment_[A-Za-z0-9_-]+/.+',name) or re.fullmatch(r'artifacts/NS_P14_V06_ALIGNMENT_[A-Za-z0-9_-]+\.zip',name),name
frozen='audit/run18/RequestedGoals.lean';assert sha((ROOT/frozen).read_bytes())=='86a0a18eff0632cb915d67748dcef47a88991cebf287ef95750f58b450bea689'
summary=load(RUN+'/verification.json');snapshot=load(RUN+'/snapshot.json');assert summary['proof_snapshot_commit']==snapshot['proof_snapshot_commit']==PROOF;assert summary['baseline_commit']==snapshot['baseline_commit']==BASE
assert summary['status']=='V06_ALIGNMENT_COMPLETE' and summary['v06_alignment_complete'] is True
assert summary['scope']==['endpoint','antipodal_integer_payment','nonantipodal_integer_payment','higher_from_second','dense_two_branches']
assert snapshot['mathlib_commit']=='139105d28c7685a154cb3093f79edb2e16708099';assert 'version 4.36.0-rc2,' in snapshot['lean_version'];assert (ROOT/'lean-toolchain').read_text().strip().endswith('v4.36.0-rc2')
assert load('lake-manifest.json')['packages'][0] # exact pin separately searched below
assert any(p.get('name')=='mathlib' and p.get('rev')==snapshot['mathlib_commit'] for p in load('lake-manifest.json')['packages'])
assert summary['not_claimed']==['N4','Run19','all_P14'] and summary['inherited_run18_complete_preserved'] is True
checks=summary['checks'];assert len(checks)==289 and len({r['name'] for r in checks})==289
assert load(RUN+'/checks.in_progress.json')==checks
for r in checks:
 assert r['exit_code']==0 and r['passed'] is True
 suffix='.log.gz' if r['name'] in {'environment_axioms','base_environment_types'} else '.log';p=V/(r['name']+suffix)
 text=gzip.decompress(p.read_bytes()).decode() if suffix.endswith('gz') else p.read_text()
 assert not re.search(r'\bwarning:',text),r['name']
old=load(R16+'/verification.json');mapping=load(RUN+'/COMMAND_MAP.json');by={r['name']:r for r in checks}
assert len(old['checks'])==len(mapping)==280 and len(old['fixture_order'])==268
assert [r['name'] for r in mapping]==[r['name'] for r in old['checks']]
for prior,mapped in zip(old['checks'],mapping):
 expected=[a.replace(R16+'/',RUN+'/') for a in prior['command']]
 assert mapped['old_command']==prior['command'] and mapped['new_command']==expected and by[prior['name']]['command']==expected
 assert not any(R16+'/' in a for a in by[prior['name']]['command'])
fixtures=summary['fixture_order'];assert len(fixtures)==273 and len(set(fixtures))==273
newfixtures={n for n in policy['new_files'] if n.endswith('.lean') and n.startswith(('tests/','audit/'))}
assert set(fixtures)==set(old['fixture_order'])|newfixtures
positions={n:i for i,n in enumerate(fixtures)}
for path in fixtures:
 matches=[r for r in checks if path in r['command']];assert len(matches)==1
 c=matches[0]['command'];assert c[:6]==['lake','env','lean','-j1','-M12288',path] and '-o' in c
 for dep in re.findall(r'^\s*(?:public\s+)?import\s+((?:tests|audit)\.[\w.]+)',(ROOT/path).read_text(),re.M):assert positions[dep.replace('.','/')+'.lean']<positions[path]
assert set(by)-{r['name'] for r in old['checks']}=={r['name'] for r in checks if r['name'].startswith('v06_fixture_')}|{'v06_routes','v06_alignment_controls','base_build','base_environment_types'}

def raw_rows(name):
 objects=[json.loads(s) for s in gzip.decompress((V/name).read_bytes()).decode().splitlines() if s.startswith('{')]
 meta=[o for o in objects if o.get('audit_metadata') is True];assert len(meta)==1
 return [o for o in objects if not o.get('audit_metadata')],meta[0]
raw,metadata=raw_rows('environment_axioms.log.gz');base_raw,base_metadata=raw_rows('base_environment_types.log.gz')
decls=json.loads(gzip.decompress((V/'declarations.json.gz').read_bytes()));base=json.loads(gzip.decompress((V/'base_declarations.json.gz').read_bytes()))
assert base==base_raw and len(base)==70
assert len(raw)==len(decls)==10713 and len({r['name'] for r in raw})==10713
saved={r['name']:r for r in decls};typed={p[:-5].replace('/','.') for p in allowed|newfixtures|{'NSP14/Width/IntegerPayment.lean','NSP14/Width/HigherFromSecond.lean'}}-{'audit.v06_alignment.RouteChecks'}
assert len(typed)==17
for r in raw:
 now=saved[r['name']]
 for key in ['name','module','axioms','type','explicit_type']:assert now.get(key)==r.get(key)
 assert now['exported_kind']==r['kind'];assert now['source']==r['module'].replace('.','/')+'.lean';assert now['source_sha256']==source[now['source']]
 assert set(r['axioms'])<={'propext','Classical.choice','Quot.sound'} and r['name'] not in r['axioms']
 if r['module'] in typed:assert 'type' in r and 'explicit_type' in r
assert typed<={r['module'] for r in raw if 'type' in r and 'explicit_type' in r}
for prior in base:
 assert not prior['name'].startswith('_private.')
 now=saved[prior['name']];assert prior['type']==now['type'] and prior['explicit_type']==now['explicit_type']
assert typed|{'NSP14','audit.v06_alignment.RouteChecks'}<=set(metadata['imported_modules'])
assert load(RUN+'/environment_import_coverage.json')==metadata
coverage=load(RUN+'/audit_coverage.json');assert set(coverage['typed_modules'])==typed and coverage['base_public_exports_compared']==len(base)
assert coverage['module_declaration_counts']=={m:sum(r['module']==m for r in raw) for m in typed}
controls=load(RUN+'/alignment_controls.json');assert controls['status']=='PASS_V06_ALIGNMENT_NEGATIVE_CONTROLS' and controls['count']==len(controls['controls'])==24;assert len({r['control'] for r in controls['controls']})==24 and all(r['passed'] is True for r in controls['controls'])
assert 'PASS_V06_ALIGNMENT_NEGATIVE_CONTROLS 24' in (V/'v06_alignment_controls.log').read_text()
assert all('rejection' in r for r in controls['controls'] if r['control'] not in {'unaltered_disposable_snapshot','public_proof_stub_is_accepted'})
fresh=load(RUN+'/fresh_cache.json');assert fresh['whole_project_lib_and_ir'] is True and fresh['shared_mathlib_cache_untouched'] is True;assert {r['from'] for r in fresh['moved']}=={'.lake/build/lib/lean','.lake/build/ir'}
build=(V/'build.log').read_text();assert build.rstrip().endswith('Build completed successfully (6658 jobs).')
built=set(re.findall(r'\bBuilt (NSP14(?:\.[\w]+)*)\s',build));assert len(built)==684
assert {p[:-5].replace('/','.') for p in allowed}|{'NSP14','NSP14.Width.IntegerPayment','NSP14.Width.HigherFromSecond','NSP14.Endpoint.RowPackage','NSP14.Endpoint.SocleBounds','NSP14.Width.Closure'}<=built
assert 'Build completed successfully' in (V/'base_build.log').read_text()
spec=importlib.util.spec_from_file_location('runtime_routes',ROOT/'scripts/check_v06_routes.py');route_module=importlib.util.module_from_spec(spec);spec.loader.exec_module(route_module)
routes=route_module.check();assert load(RUN+'/routes.json')==routes and len(routes['routes'])==13
result={'verdict':'PASS_WITH_EXACT_SCOPE','critical':0,'important':0,'minor':0,'reviewed_commit':EVID,'evidence_commit':EVID,'proof_snapshot_commit':PROOF,'baseline_commit':BASE,'verification':RUN,'source_files':len(source),'evidence_files_excluding_manifest':len(manifest),'preserved_evidence_files':len(retained),'baseline_files':len(bt),'checks':len(checks),'fixture_count':len(fixtures),'environment_declarations':len(decls),'typed_modules':len(typed),'base_public_exports_compared':len(base),'negative_controls':len(controls['controls']),'coldbuilt_modules':len(built),'command_seconds':round(sum(r['seconds'] for r in checks),3),'source_manifest_sha256':sha((V/'SOURCE_SHA256.json').read_bytes()),'verification_manifest_sha256':sha((V/'MANIFEST_SHA256.json').read_bytes()),'verification_summary_sha256':sha((V/'verification.json').read_bytes()),'raw_environment_sha256':sha((V/'environment_axioms.log.gz').read_bytes()),'raw_base_environment_sha256':sha((V/'base_environment_types.log.gz').read_bytes()),'build_log_sha256':sha((V/'build.log').read_bytes()),'static_report_sha256':sha(Path('/tmp/v06-infra-independent-review.md').read_bytes())}
Path('/tmp/v06-runtime-own-result.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
