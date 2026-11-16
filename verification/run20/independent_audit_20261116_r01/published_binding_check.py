from pathlib import Path,PurePosixPath
import subprocess,hashlib,json,gzip,zipfile,re
ROOT=Path('/workspace/NS-P14-Lean-run18');OUT=ROOT/'verification/run20/runs/release_20261116_r03'
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
s=json.loads((OUT/'verification.json').read_text());source=json.loads((OUT/'SOURCE_SHA256.json').read_text());evidence=json.loads((OUT/'MANIFEST_SHA256.json').read_text())
completion=json.loads((ROOT/'verification/run20/RUN20_COMPLETE_20261116_R03.json').read_text());review=json.loads((ROOT/'verification/run20/review/final_20261116_r03.json').read_text())
assert s['status']=='PASS_RUN20_COMPLETE_VALIDATION' and s['closed_ids']==['I_MAIN','I_PARTITION'] and not s['unproved_ids']
assert len(s['checks'])==335 and len(s['fixture_order'])==len(set(s['fixture_order']))==311
assert all(c['passed']is True and c['exit_code']==0 for c in s['checks'])
for n,h in {**source,**evidence}.items():assert sha(ROOT/n)==h,n
assert set(evidence)=={str(p.relative_to(ROOT))for p in OUT.rglob('*')if p.is_file()and p!=OUT/'MANIFEST_SHA256.json'}
for commit in [s['proof_snapshot_commit'],review['reviewed_commit']]:git_bind(commit,source)
git_bind(review['reviewed_commit'],{**evidence,str((OUT/'MANIFEST_SHA256.json').relative_to(ROOT)):sha(OUT/'MANIFEST_SHA256.json')})
assert review['source_snapshot_commit']==s['proof_snapshot_commit'] and review['verdict']=='PASS'
assert all(review[k]==0 for k in ['critical','important','minor']) and review['pending']==review['declined']==[]
assert review['verification_summary_sha256']==sha(OUT/'verification.json') and review['verification_manifest_sha256']==sha(OUT/'MANIFEST_SHA256.json')
assert review['source_manifest_sha256']==sha(OUT/'SOURCE_SHA256.json') and review['review_report_sha256']==sha(ROOT/review['review_report'])
git_bind(completion['review']['commit'],{p:sha(ROOT/p)for p in [completion['review']['decision'],review['review_report']]})

modules=set(s['normal_explicit_type_and_axiom_coverage']);expected=set(json.loads(gzip.decompress((ROOT/'verification/run20/sources/expected_declarations.json.gz').read_bytes())))
allowed={'propext','Classical.choice','Quot.sound'};saved={};types={};own_modules=set();private=0
main_types=json.loads((ROOT/'verification/run20/sources/main_type_fully_explicit.json').read_text());main_seen=set()
for row in array_rows(OUT/'declarations.json.gz'):
 name=row['name'];assert name not in saved and row['module']in modules,name
 assert {'type','explicit_type','kernel_type','axioms','universe_parameters','source_sha256'}<=row.keys(),name
 assert row['kernel_alpha_roundtrip']is True and row['kernel_dag_roundtrip']is True,name
 assert set(row['axioms'])<=allowed and name not in row['axioms'],name
 assert row['source_sha256']==source[row['module'].replace('.','/')+'.lean'],name
 if name in main_types:
  for k,value in main_types[name].items():assert row['pretty_explicit_type'if k=='explicit_type'else k]==value,(name,k)
  main_seen.add(name)
 private+=name.startswith('_private.');own_modules.add(row['module']);types[name]=type_sha(row)
 del row['source_sha256'];saved[name]=row_sha(row)
assert set(saved)==expected and len(saved)==15774 and main_seen==set(main_types)
parts=OUT/'environment_parts';snapshot=json.loads((parts/'snapshot.json').read_text());selected=set();raw_names=set();raw_hashes=[]
assert set(snapshot['modules'])==modules
for n,h in snapshot['source_sha256'].items():assert source[n]==h,n
for p in sorted(parts.glob('Part*.process.json')):
 process=json.loads(p.read_text());assert process['passed']is True and process['exit_code']==0,p
 subset=set(process['selected_modules']);assert not selected&subset,p;selected|=subset
 base=p.name.removesuffix('.process.json');log=gzip.decompress((parts/(base+'.log.gz')).read_bytes()).decode()
 assert not re.search(r'\bwarning:',log),p
 objects=[json.loads(line)for line in log.splitlines()if line.startswith('{')]
 inventories=[r['declaration_inventory']for r in objects if 'declaration_inventory'in r];metas=[r for r in objects if r.get('audit_metadata')]
 assert len(inventories)==len(metas)==1 and modules<=set(metas[0]['imported_modules']),p
 local=set();h=hashlib.sha256()
 with gzip.open(parts/(base+'.rows.jsonl.gz'),'rb')as f:
  for line in f:
   h.update(line);row=json.loads(line);name=row['name'];assert name not in raw_names and row['module']in subset,(p,name)
   assert row_sha(row)==saved[name],name;raw_names.add(name);local.add(name)
 assert h.hexdigest()==process['row_stream_uncompressed_sha256'] and local==set(inventories[0]),p
 raw_hashes.append(h.hexdigest())
assert selected==modules and raw_names==expected
base_count=0;public_count=0
for row in array_rows(ROOT/'verification/run20/sources/base_declarations.json.gz'):
 base_count+=1;assert row['name']in saved,row['name']
 if not row['name'].startswith('_private.'):
  assert type_sha(row)==types[row['name']],row['name'];public_count+=1
assert base_count==15542 and public_count==11928

archive=ROOT/completion['archive']['archive'];archive_sha=sha(archive);assert archive_sha==completion['archive']['sha256']
with zipfile.ZipFile(archive)as z:
 names=z.namelist();assert len(names)==len(set(names))==2168 and z.testzip()is None
 assert all(not PurePosixPath(n).is_absolute()and'..'not in PurePosixPath(n).parts and'\\'not in n for n in names)
 bundle=json.loads(z.read('BUNDLE_SHA256.json'));assert set(names)==set(bundle)|{'BUNDLE_SHA256.json'}
 for n,want in bundle.items():
  with z.open(n)as f:assert digest_stream(f)==want,n
 for n,want in {**source,**evidence,str((OUT/'MANIFEST_SHA256.json').relative_to(ROOT)):sha(OUT/'MANIFEST_SHA256.json'),review['review_report']:sha(ROOT/review['review_report']),completion['review']['decision']:sha(ROOT/completion['review']['decision'])}.items():assert bundle[n]==want,n
 binding=json.loads(z.read('RUN20_BINDING.json'))
 for k in ['proof_snapshot_commit','reviewed_evidence_commit','review_commit']:assert binding[k]==completion['archive'][k],k
 assert z.read('REPRODUCE.md').decode().find('not an offline toolchain/mathlib checkout')>=0

git_bind(completion['normal_push']['pushed_package_commit'],{completion['archive']['archive']:archive_sha})
chain=[s['proof_snapshot_commit'],review['reviewed_commit'],completion['review']['commit'],completion['normal_push']['pushed_package_commit'],'a5e122a4d09536b1609c5faa8d419f8faf81671f']
for a,b in zip(chain,chain[1:]):subprocess.run(['git','merge-base','--is-ancestor',a,b],cwd=ROOT,check=True)
assert completion['status']=='RUN20_COMPLETE' and completion['run20_complete']is True and completion['all_P14_complete']is True and not completion['remaining_required_work']
result={'status':'PASS_PUBLISHED_RUN20_GIT_RAW_DECLARATIONS_REVIEW_AND_ZIP','proof_snapshot_commit':s['proof_snapshot_commit'],'reviewed_commit':review['reviewed_commit'],'source_entries':len(source),'evidence_entries':len(evidence),'checks':len(s['checks']),'fixtures':len(s['fixture_order']),'declarations':len(saved),'typed_modules':len(modules),'declaration_owning_modules':len(own_modules),'private_declarations':private,'base_declarations':base_count,'preserved_public_type_pairs':public_count,'allowed_axioms':sorted(allowed),'all_raw_stream_rows_equal_saved_rows':True,'reviewed_commit_source_entries_all_match':True,'zip_entries':2168,'zip_sha256':archive_sha,'zip_safe_paths_CRC_and_all_payload_hashes':True,'archive_Git_bytes_at_package_commit_match':True,'all_P14_completion_receipt':True}
Path('/tmp/run20-published-bindings.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
