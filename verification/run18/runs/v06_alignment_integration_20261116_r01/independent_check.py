from pathlib import Path,PurePosixPath
import hashlib,json,subprocess,zipfile
PUBROOT=Path('/tmp/ns-p14-v06-alignment-20261116');INTROOT=Path('/tmp/ns-p14-v06-work-integration-20261116')
PUB='748f2d04d269eed4ea7aed09fd1df4f013c254ab';FINAL='835a14c2f4bd8c37c24337137369067b2dab5829';MERGE='4c2c1ecbba7e819c49eebddccb81905c46b87b44';CON='306df7bc605477faa7891230879ee609e469805e';PROOF='d446fc2f18f7a8603d1eedd446e93810dc44d01c';EVID='0880f6f30836873036b4d9908b7dcef50125d2c8';REVIEW='ae8dae2f6ba9c9e07ec2a3040c6e49984099ed3f'
RUN='verification/run18/runs/v06_alignment_20261115T152000Z_r01';REVDIR='verification/run18/runs/v06_alignment_review_20261116_r01';INTEG='verification/run18/runs/v06_alignment_integration_20261116_r01';ARCH='artifacts/NS_P14_V06_ALIGNMENT_20261116_R01.zip'
def git(root,*args):return subprocess.check_output(['git',*args],cwd=root)
def sha(b):return hashlib.sha256(b).hexdigest()
def oid(b):return hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
def tree(root,c):
 out={}
 for row in git(root,'ls-tree','-rz','--full-tree',c).split(b'\0'):
  if row:
   meta,n=row.split(b'\t',1);out[n.decode()]=meta.split()[2].decode()
 return out
assert git(PUBROOT,'rev-parse','HEAD').decode().strip()==PUB
assert git(INTROOT,'rev-parse','HEAD').decode().strip()==FINAL
pt,et,rt,ut=[tree(PUBROOT,c) for c in [PROOF,EVID,REVIEW,PUB]]
ct,mt,ft=[tree(INTROOT,c) for c in [CON,MERGE,FINAL]]
archive=(PUBROOT/ARCH).read_bytes();assert len(archive)==11368725;ah=sha(archive);assert ah=='b397bccb046d98458095353c039c27cc5e86b82628e20603eee09fff2def2670'
assert (INTROOT/ARCH).read_bytes()==archive and oid(archive)==ut[ARCH]==mt[ARCH]==ft[ARCH]
with zipfile.ZipFile(PUBROOT/ARCH) as z:
 names=z.namelist();assert len(names)==len(set(names))==1819 and z.testzip() is None
 assert all(not PurePosixPath(n).is_absolute() and '..' not in PurePosixPath(n).parts and '\\' not in n for n in names)
 payload={n:z.read(n) for n in names}
bundle=json.loads(payload['BUNDLE_SHA256.json']);assert set(bundle)==set(names)-{'BUNDLE_SHA256.json'}
for n,h in bundle.items():assert sha(payload[n])==h
receipt=json.loads(payload['V06_ALIGNMENT_RECEIPT.json']);assert receipt['proof_snapshot_commit']==PROOF and receipt['evidence_commit']==receipt['reviewed_commit']==EVID and receipt['publication_head']==REVIEW
assert receipt['verification']==RUN and receipt['review']==REVDIR+'/decision.json' and receipt['not_claimed']==['N4','Run19','all_P14']
source=json.loads(payload[RUN+'/SOURCE_SHA256.json']);evidence=json.loads(payload[RUN+'/MANIFEST_SHA256.json']);summary=json.loads(payload[RUN+'/verification.json']);decision=json.loads(payload[REVDIR+'/decision.json'])
assert len(source)==1497 and len(evidence)==317
expected=set(source)|set(evidence)|{RUN+'/MANIFEST_SHA256.json',REVDIR+'/decision.json',REVDIR+'/report.md','V06_ALIGNMENT_RECEIPT.json','BUNDLE_SHA256.json'};assert set(payload)==expected
assert decision['proof_snapshot_commit']==PROOF and decision['evidence_commit']==decision['reviewed_commit']==EVID
assert decision['verdict']=='PASS' and all(decision[k]==0 for k in ['critical','important','minor']) and decision['pending']==decision['declined']==[] and decision['verifier_independently_reviewed'] is True
assert decision['scope']==receipt['scope']==summary['scope'] and decision['v06_alignment_complete'] is True
for k,p in [('verification_summary_sha256','verification.json'),('verification_manifest_sha256','MANIFEST_SHA256.json'),('source_manifest_sha256','SOURCE_SHA256.json')]:assert decision[k]==sha(payload[RUN+'/'+p])
assert decision['review_report']==REVDIR+'/report.md' and decision['review_report_sha256']==sha(payload[decision['review_report']])
for n,h in source.items():assert sha(payload[n])==h and oid(payload[n])==pt[n]==et[n]==rt[n]==ut[n]
for n,h in evidence.items():assert sha(payload[n])==h and oid(payload[n])==et[n]==rt[n]==ut[n]==mt[n]==ft[n]
assert oid(payload[RUN+'/MANIFEST_SHA256.json'])==et[RUN+'/MANIFEST_SHA256.json']==rt[RUN+'/MANIFEST_SHA256.json']==ut[RUN+'/MANIFEST_SHA256.json']==ft[RUN+'/MANIFEST_SHA256.json']
for n in names:
 if n in {'BUNDLE_SHA256.json','V06_ALIGNMENT_RECEIPT.json'}:continue
 assert payload[n]==(PUBROOT/n).read_bytes() and oid(payload[n])==ut[n]
for n in [REVDIR+'/decision.json',REVDIR+'/report.md']:assert oid(payload[n])==rt[n]==ut[n]==mt[n]==ft[n]
report=payload[REVDIR+'/report.md']
for n in ['math_review.md','infrastructure_review.md','runtime_review.md']:assert (PUBROOT/REVDIR/n).read_bytes() in report
assert sha((PUBROOT/REVDIR/'infrastructure_review.md').read_bytes())=='5433e2bca2367a48db2dbe807777fa0b7eb9bc4c9f0478c136acfbab83edc0a1'
assert sha((PUBROOT/REVDIR/'runtime_review.md').read_bytes())=='5cf916a68bcd6c05b948da2ce737c53264091be038aea3a793dd0b0f1413a7bb'
review_manifest=json.loads((PUBROOT/REVDIR/'REVIEW_SHA256.json').read_text())
for n,h in review_manifest.items():assert sha((PUBROOT/n).read_bytes())==h and oid((PUBROOT/n).read_bytes())==rt[n]==ut[n]==mt[n]==ft[n]
for a,b in [(PROOF,EVID),(EVID,REVIEW),(REVIEW,PUB),(PUB,MERGE),(CON,MERGE),(MERGE,FINAL)]:subprocess.run(['git','merge-base','--is-ancestor',a,b],cwd=INTROOT,check=True)
parents=git(INTROOT,'rev-list','--parents','-n','1',MERGE).decode().split()[1:];assert set(parents)=={CON,PUB}
expected_con={'docs/superpowers/plans/2026-11-15-run19-v06-n4-small-closure-order.md','docs/superpowers/specs/2026-11-15-run19-v06-input-scope.md','docs/superpowers/specs/2026-11-15-run19-v06-n4-checked-contracts.md','verification/run19/planning/v06_n4_publication_20261115/published_math_only.json','verification/run19/planning/v06_n4_publication_20261115/receipt.json'}
difference={n for n in set(ut)|set(mt) if ut.get(n)!=mt.get(n)};assert difference==expected_con
for n in expected_con:assert ct[n]==mt[n]==ft[n] and oid((INTROOT/n).read_bytes())==ct[n]
exceptions=set(source)&expected_con;assert len(exceptions)==2
for n,h in source.items():
 if n not in exceptions:assert sha((INTROOT/n).read_bytes())==h and ft[n]==pt[n]
assert len(source)-len(exceptions)==1495
added={n for n in set(mt)|set(ft) if mt.get(n)!=ft.get(n)};assert added=={INTEG+'/check_integration.py',INTEG+'/receipt.json'}
for n in added:assert n not in mt and oid((INTROOT/n).read_bytes())==ft[n]
integ=json.loads((INTROOT/INTEG/'receipt.json').read_text());assert integ['merged_commit']==MERGE and integ['concurrent_work_commit']==CON and integ['certified_publication_commit']==PUB and integ['certified_proof_commit']==PROOF and integ['certified_evidence_commit']==EVID
assert set(integ['preserved_concurrent_paths'])==expected_con and integ['certified_source_files_identical_except_concurrent_run19_docs']==1495 and set(integ['concurrent_existing_source_manifest_exceptions'])==exceptions
assert integ['no_lean_test_verifier_or_pin_changes'] is True and integ['certified_evidence_preserved'] is True
assert not git(INTROOT,'diff','--name-only',PUB,FINAL,'--','NSP14','NSP14.lean','tests','audit','scripts','lean-toolchain','lakefile.toml','lake-manifest.json').strip()
result={'verdict':'PASS_WITH_EXACT_SCOPE','critical':0,'important':0,'minor':0,'publication_commit':PUB,'integration_merge_commit':MERGE,'integration_receipt_commit':FINAL,'concurrent_commit':CON,'proof_snapshot_commit':PROOF,'evidence_reviewed_commit':EVID,'review_commit':REVIEW,'archive':ARCH,'archive_sha256':ah,'archive_bytes':len(archive),'archive_entries':len(names),'source_files':len(source),'run_evidence_files_excluding_manifest':len(evidence),'concurrent_files_preserved':len(expected_con),'source_files_unchanged_after_integration':1495,'source_doc_exceptions':sorted(exceptions),'integration_receipt_sha256':sha((INTROOT/INTEG/'receipt.json').read_bytes()),'integration_checker_sha256':sha((INTROOT/INTEG/'check_integration.py').read_bytes()),'archive_bundle_manifest_sha256':sha(payload['BUNDLE_SHA256.json']),'archive_receipt_sha256':sha(payload['V06_ALIGNMENT_RECEIPT.json']),'review_decision_sha256':sha(payload[REVDIR+'/decision.json']),'review_report_sha256':sha(payload[REVDIR+'/report.md'])}
Path('/tmp/v06-publication-own-result.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
