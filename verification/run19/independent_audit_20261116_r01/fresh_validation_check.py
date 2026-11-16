from pathlib import Path
import gzip, hashlib, json, subprocess
root=Path('/workspace/NS-P14-Lean-run18')
out=root/'verification/run19/runs/independent_audit_20261116_r01'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
s=json.loads((out/'verification.json').read_text())
assert s['status']=='PASS_RUN19_COMPLETE_VALIDATION' and s['proof_snapshot_commit']=='07fe1ed952ae31ce01255ce53df538bf0a76d5cc'
assert len(s['checks'])==318 and len(s['fixture_order'])==299 and len(set(s['fixture_order']))==299
assert all(c['passed'] is True and c['exit_code']==0 for c in s['checks'])
assert len(s['closed_ids'])==10 and not s['unproved_ids']
manifest=json.loads((out/'MANIFEST_SHA256.json').read_text())
assert set(manifest)=={str(p.relative_to(root))for p in out.rglob('*')if p.is_file()and p.name!='MANIFEST_SHA256.json'}
source=json.loads((out/'SOURCE_SHA256.json').read_text());retained=json.loads((out/'INHERITED_EVIDENCE_SHA256.json').read_text())
for name,h in {**source,**manifest,**retained}.items():assert sha(root/name)==h,name
names=list(source)
raw=subprocess.check_output(['git','cat-file','--batch'],cwd=root,input=''.join(s['proof_snapshot_commit']+':'+n+'\n'for n in names).encode());pos=0
for name in names:
 end=raw.index(b'\n',pos);header=raw[pos:end].split();assert len(header)==3,(name,header)
 size=int(header[2]);data=raw[end+1:end+1+size];assert hashlib.sha256(data).hexdigest()==source[name],name
 pos=end+1+size+1
assert pos==len(raw)
rows=json.loads(gzip.decompress((out/'declarations.json.gz').read_bytes()))
objects=[json.loads(line)for line in gzip.decompress((out/'environment_axioms.log.gz').read_bytes()).decode().splitlines()if line.startswith('{')]
meta=[r for r in objects if r.get('audit_metadata')];records=[r for r in objects if not r.get('audit_metadata')]
assert len(meta)==1 and len(rows)==len(records)==s['environment_declarations']==12792
by={r['name']:r for r in rows};assert len(by)==len(rows)
allowed={'propext','Classical.choice','Quot.sound'};typed=set(s['normal_explicit_type_and_axiom_coverage'])
for r in records:
 saved=by[r['name']]
 assert all(saved[k]==value for k,value in r.items()),r['name']
 assert set(r['axioms'])<=allowed and r['name']not in r['axioms'],r['name']
 if r['module'] in typed:assert 'type'in r and'explicit_type'in r,r['name']
 assert saved['source_sha256']==source[r['module'].replace('.','/')+'.lean']
assert typed|set(s['verified_import_only_modules'])|{'NSP14'}<=set(meta[0]['imported_modules'])
helper=json.loads((out/'named_helper_coverage.json').read_text())
for mod,names in helper['required'].items():
 for name in names:assert by[name]['module']==mod and {'type','explicit_type','axioms'}<=by[name].keys(),name
result={'status':'PASS_INDEPENDENT_COLD_EVIDENCE_CROSSCHECK','proof_snapshot_commit':s['proof_snapshot_commit'],
 'checks':318,'fixtures':299,'declarations':len(rows),'typed_declarations':sum('type'in r and'explicit_type'in r for r in rows),
 'typed_modules':len(typed),'import_only_modules':len(s['verified_import_only_modules']),'canonical_helpers':helper['count'],
 'allowed_axioms':sorted(allowed),'source_entries':len(source),'evidence_entries':len(manifest),'retained_entries':len(retained),
 'verification_sha256':sha(out/'verification.json'),'manifest_sha256':sha(out/'MANIFEST_SHA256.json'),
 'source_manifest_sha256':sha(out/'SOURCE_SHA256.json'),'fresh_whole_project_cache':s['fresh_whole_project_cache']}
Path('/tmp/run19-independent-fresh-check.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
