from pathlib import Path
import gzip,hashlib,json,subprocess,zipfile
root=Path('/workspace/NS-P14-Lean-run18');out=root/'verification/run19/runs/release_20261116_r03';summary=json.loads((out/'verification.json').read_text());review=json.loads((root/'verification/run19/review/final_20261116_r03.json').read_text())
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
source=json.loads((out/'SOURCE_SHA256.json').read_text());ev=json.loads((out/'MANIFEST_SHA256.json').read_text())
def batch_bind(commit,manifest):
 names=list(manifest);raw=subprocess.check_output(['git','cat-file','--batch'],cwd=root,input=''.join(commit+':'+n+'\n'for n in names).encode());pos=0
 for name in names:
  end=raw.index(b'\n',pos);header=raw[pos:end].split();assert len(header)==3,(name,header)
  size=int(header[2]);data=raw[end+1:end+1+size];assert hashlib.sha256(data).hexdigest()==manifest[name],(commit,name)
  pos=end+1+size+1
 assert pos==len(raw)
for f,h in {**source,**ev}.items():assert sha(root/f)==h,f
assert set(ev)=={str(p.relative_to(root))for p in out.rglob('*')if p.is_file()and p.name!='MANIFEST_SHA256.json'}
for commit in [summary['proof_snapshot_commit'],review['reviewed_commit']]:batch_bind(commit,source)
batch_bind(review['reviewed_commit'],{**ev,str((out/'MANIFEST_SHA256.json').relative_to(root)):sha(out/'MANIFEST_SHA256.json')})
rows=json.loads(gzip.decompress((out/'declarations.json.gz').read_bytes()));objects=[json.loads(line)for line in gzip.decompress((out/'environment_axioms.log.gz').read_bytes()).decode().splitlines()if line.startswith('{')]
raw=[r for r in objects if not r.get('audit_metadata')];metadata=[r for r in objects if r.get('audit_metadata')]
assert len(metadata)==1 and len(rows)==len(raw)==12792
by={r['name']:r for r in rows};assert len(by)==len(rows)
allowed={'propext','Classical.choice','Quot.sound'}
for r in raw:
 saved=by[r['name']]
 for k,value in r.items():assert saved[k]==value,(r['name'],k)
 assert set(r['axioms'])<=allowed and r['name']not in r['axioms'],r
 assert saved['source_sha256']==sha(root/(r['module'].replace('.','/')+'.lean'))
for c in summary['checks']:assert c['passed'] is True and c['exit_code']==0,c
assert len(summary['checks'])==318 and len(summary['fixture_order'])==299
assert review['verification_summary_sha256']==sha(out/'verification.json') and review['verification_manifest_sha256']==sha(out/'MANIFEST_SHA256.json')
assert review['review_report_sha256']==sha(root/review['review_report'])
complete=json.loads((root/'verification/run19/RUN19_COMPLETE_20261116_R03.json').read_text())
archive=root/'artifacts/NS_P14_LEAN_RUN19_COMPLETE_20261116_R03.zip';package=json.loads((root/'verification/run19/publication/package_20261116_r03.json').read_text());assert sha(archive)==package['sha256']
with zipfile.ZipFile(archive)as z:
 assert z.testzip()is None and len(z.namelist())==len(set(z.namelist()))==1959
 bundle=json.loads(z.read('BUNDLE_SHA256.json'));assert set(z.namelist())==set(bundle)|{'BUNDLE_SHA256.json'}
 for name,h in bundle.items():assert hashlib.sha256(z.read(name)).hexdigest()==h,name
 for name in source:assert hashlib.sha256(z.read(name)).hexdigest()==source[name],name
 for name in ev:assert hashlib.sha256(z.read(name)).hexdigest()==ev[name],name
 assert z.read(review['review_report'])==(root/review['review_report']).read_bytes()
result=dict(status='PASS_PUBLISHED_PROOF_EVIDENCE_REVIEW_AND_ZIP_ACTUAL_BINDINGS',proof_snapshot=summary['proof_snapshot_commit'],reviewed_commit=review['reviewed_commit'],
 source_entries=len(source),evidence_entries=len(ev),reviewed_commit_source_entries_all_match=True,commands=318,fixtures=299,declarations=len(rows),
 typed_declarations=sum('type'in r and'explicit_type'in r for r in rows),axioms=sorted(allowed),zip_entries=1959,zip_sha256=sha(archive),
 source_review_guard_gap_affects_this_published_bundle=False,completion_receipt_status=complete.get('status'))
Path('/tmp/run19-audit-actual-bindings.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
