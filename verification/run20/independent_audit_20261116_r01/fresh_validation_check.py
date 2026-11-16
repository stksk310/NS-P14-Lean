from pathlib import Path,PurePosixPath
import subprocess,hashlib,json,gzip,zipfile,re
ROOT=Path('/workspace/NS-P14-Lean-run18');OUT=ROOT/'verification/run20/runs/independent_audit_20261116_r01'
def digest_stream(f):
 h=hashlib.sha256()
 while True:
  b=f.read(1024*1024)
  if not b:return h.hexdigest()
  h.update(b)
def sha(p):
 with p.open('rb')as f:return digest_stream(f)
def array_rows(p):
 dec=json.JSONDecoder()
 with gzip.open(p,'rt')as f:
  buf='';eof=False;first=True;opened=False
  while True:
   buf=buf.lstrip()
   if not buf and not eof:
    block=f.read(65536);eof=not block;buf+=block;continue
   if not opened:
    assert buf.startswith('['),p;buf=buf[1:];opened=True;continue
   if buf.startswith(']'):
    assert not (buf[1:]+f.read()).strip(),p;return
   if not first:
    assert buf.startswith(','),(p,buf[:50]);buf=buf[1:].lstrip()
   while True:
    try:row,end=dec.raw_decode(buf);break
    except json.JSONDecodeError:
     more=f.read(65536);assert more,(p,buf[:50]);buf+=more
   yield row
   buf=buf[end:];first=False

def git_bind(commit,manifest):
 q=subprocess.Popen(['git','cat-file','--batch'],cwd=ROOT,stdin=subprocess.PIPE,stdout=subprocess.PIPE)
 try:
  for name,want in manifest.items():
   q.stdin.write((commit+':'+name+'\n').encode());q.stdin.flush();header=q.stdout.readline().split()
   assert len(header)==3 and header[1]==b'blob',(commit,name,header)
   remaining=int(header[2]);h=hashlib.sha256()
   while remaining:
    b=q.stdout.read(min(remaining,1024*1024));assert b,(commit,name);remaining-=len(b);h.update(b)
   assert q.stdout.read(1)==b'\n' and h.hexdigest()==want,(commit,name)
  q.stdin.close();assert q.wait()==0
 finally:
  if q.poll()is None:q.kill();q.wait()

def row_sha(row):return hashlib.sha256(json.dumps(row,sort_keys=True,ensure_ascii=False,separators=(',',':')).encode()).hexdigest()
def type_sha(row):return hashlib.sha256(json.dumps([row['type'],row['explicit_type']],ensure_ascii=False).encode()).hexdigest()
s=json.loads((OUT/'verification.json').read_text());source=json.loads((OUT/'SOURCE_SHA256.json').read_text());evidence=json.loads((OUT/'MANIFEST_SHA256.json').read_text());retained=json.loads((OUT/'INHERITED_EVIDENCE_SHA256.json').read_text())
assert s['status']=='PASS_RUN20_COMPLETE_VALIDATION' and s['proof_snapshot_commit']=='a5e122a4d09536b1609c5faa8d419f8faf81671f'
assert s['closed_ids']==['I_MAIN','I_PARTITION'] and not s['unproved_ids']
assert len(s['checks'])==335 and len(s['fixture_order'])==len(set(s['fixture_order']))==311
assert all(c['passed']is True and c['exit_code']==0 for c in s['checks'])
assert set(evidence)=={str(p.relative_to(ROOT))for p in OUT.rglob('*')if p.is_file()and p!=OUT/'MANIFEST_SHA256.json'}
for n,h in {**source,**evidence,**retained}.items():assert sha(ROOT/n)==h,n
tracked=set(subprocess.check_output(['git','ls-files','-z','--cached'],cwd=ROOT).decode().split('\0'))
actual_retained={}
for folder in ['verification','artifacts']:
 for p in (ROOT/folder).rglob('*'):
  if not p.is_file()or p.is_relative_to(OUT):continue
  n=str(p.relative_to(ROOT))
  if n not in tracked and '__pycache__'in p.parts and p.suffix=='.pyc':continue
  actual_retained[n]=sha(p)
assert actual_retained==retained
assert source==json.loads((ROOT/'verification/run20/runs/release_20261116_r03/SOURCE_SHA256.json').read_text())
git_bind(s['proof_snapshot_commit'],source)
prior=json.loads((ROOT/'verification/run19/runs/release_20261116_r03/verification.json').read_text());old={r['name']:r for r in prior['checks']};now={r['name']:r for r in s['checks']};mapping=json.loads((OUT/'COMMAND_MAP.json').read_text())
assert len(now)==len(s['checks'])==len(mapping) and set(old)<=set(now)
for row in mapping:
 assert row['new_command']==now[row['name']]['command'] and row['old_command']==(old[row['name']]['command']if row['name']in old else None),row['name']
modules={'NSP14'}|{str(p.relative_to(ROOT))[:-5].replace('/','.')for folder in ['NSP14','tests','audit']for p in (ROOT/folder).rglob('*.lean')}
assert modules==set(s['normal_explicit_type_and_axiom_coverage']) and len(modules)==1019
assert set(s['fixture_order'])=={m.replace('.','/')+'.lean'for m in modules if m.startswith(('tests.','audit.'))}
expected=set(json.loads(gzip.decompress((ROOT/'verification/run20/sources/expected_declarations.json.gz').read_bytes())))
allowed={'propext','Classical.choice','Quot.sound'};saved={};types={};universes={};private=0;owners=set();main_types=json.loads((ROOT/'verification/run20/sources/main_type_fully_explicit.json').read_text());main_seen=set()
for row in array_rows(OUT/'declarations.json.gz'):
 name=row['name'];assert name not in saved and row['module']in modules,name
 assert {'type','explicit_type','kernel_type','axioms','universe_parameters','source_sha256'}<=row.keys(),name
 assert row['kernel_alpha_roundtrip']is True and row['kernel_dag_roundtrip']is True,name
 assert set(row['axioms'])<=allowed and name not in row['axioms'],name
 assert row['source_sha256']==source[row['module'].replace('.','/')+'.lean'],name
 if name in main_types:
  for k,value in main_types[name].items():assert row['pretty_explicit_type'if k=='explicit_type'else k]==value,(name,k)
  main_seen.add(name)
 private+=name.startswith('_private.');owners.add(row['module']);types[name]=type_sha(row);universes[name]=row['universe_parameters'];del row['source_sha256'];saved[name]=row_sha(row)
assert set(saved)==expected and len(saved)==15774 and main_seen==set(main_types)
parts=OUT/'environment_parts';selected=set();raw_names=set()
for p in sorted(parts.glob('Part*.process.json')):
 process=json.loads(p.read_text());assert process['passed']is True and process['exit_code']==0,p
 subset=set(process['selected_modules']);assert not selected&subset,p;selected|=subset
 base=p.name.removesuffix('.process.json');log=gzip.decompress((parts/(base+'.log.gz')).read_bytes()).decode();assert not re.search(r'\bwarning:',log),p
 objects=[json.loads(line)for line in log.splitlines()if line.startswith('{')];inventories=[r['declaration_inventory']for r in objects if 'declaration_inventory'in r];metas=[r for r in objects if r.get('audit_metadata')]
 assert len(inventories)==len(metas)==1 and modules<=set(metas[0]['imported_modules']),p
 local=set();h=hashlib.sha256()
 with gzip.open(parts/(base+'.rows.jsonl.gz'),'rb')as f:
  for line in f:
   h.update(line);row=json.loads(line);name=row['name'];assert name not in raw_names and row['module']in subset,(p,name)
   assert row_sha(row)==saved[name],name;raw_names.add(name);local.add(name)
 assert h.hexdigest()==process['row_stream_uncompressed_sha256']and local==set(inventories[0]),p
assert selected==modules and raw_names==expected
base_count=0;public_count=0;golden={}
for row in array_rows(ROOT/'verification/run20/sources/base_declarations.json.gz'):
 base_count+=1;assert row['name']in saved,row['name'];golden[row['name']]=row_sha(row)
 if not row['name'].startswith('_private.'):
  assert type_sha(row)==types[row['name']]and row['universe_parameters']==universes[row['name']],row['name'];public_count+=1
base_seen=set()
for row in array_rows(OUT/'base_environment_parts/declarations.json.gz'):
 assert row['name']not in base_seen and row_sha(row)==golden[row['name']],row['name'];base_seen.add(row['name'])
assert base_seen==set(golden)and base_count==15542 and public_count==11928
controls=json.loads((OUT/'guards.json').read_text());codec=json.loads((OUT/'kernel_encoding_controls/result.json').read_text())
assert controls['status']=='PASS_RUN20_NEGATIVE_CONTROLS'and controls['count']==61 and all(c['passed']for c in controls['controls'])
assert codec['status']=='PASS_COMPLETE_KERNEL_TYPE_ENCODING'and len(codec['controls'])==13 and codec['exit_code']==0
identical=sha(OUT/'declarations.json.gz')==sha(ROOT/'verification/run20/runs/release_20261116_r03/declarations.json.gz')
result={'status':'PASS_INDEPENDENT_RUN20_COLD_EVIDENCE_CROSSCHECK','proof_snapshot_commit':s['proof_snapshot_commit'],'checks':335,'fixtures':311,'declarations':len(saved),'all_typed_modules':len(modules),'declaration_owning_modules':len(owners),'import_only_modules':len(modules-owners),'private_declarations':private,'base_declarations':base_count,'preserved_public_type_and_universe_pairs':public_count,'allowed_axioms':sorted(allowed),'source_entries':len(source),'evidence_entries':len(evidence),'retained_bytes_and_fileset_entries':len(retained),'source_manifest_equals_published_R03':True,'saved_declaration_GZIP_bytes_identical_to_published_R03':identical,'all_raw_part_rows_equal_saved_rows':True,'negative_controls':61,'actual_Lean_codec_controls':13,'verification_sha256':sha(OUT/'verification.json'),'manifest_sha256':sha(OUT/'MANIFEST_SHA256.json'),'source_manifest_sha256':sha(OUT/'SOURCE_SHA256.json'),'fresh_whole_project_cache':s['fresh_whole_project_cache'],'baseline_cache_source_identity_receipt':'/tmp/run20-baseline-donor-receipt.json'}
Path('/tmp/run20-independent-fresh-check.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
