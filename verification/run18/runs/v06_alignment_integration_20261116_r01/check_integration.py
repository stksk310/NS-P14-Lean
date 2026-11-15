#!/usr/bin/env python3
"""Record a docs-only concurrent integration without relabeling its proof certificate."""
import argparse,hashlib,json,pathlib,subprocess
p=argparse.ArgumentParser();p.add_argument('--root',required=True);p.add_argument('--publication',required=True);p.add_argument('--output',required=True);a=p.parse_args()
r=pathlib.Path(a.root)
git=lambda *args:subprocess.check_output(['git',*args],cwd=r)
sha=lambda data:hashlib.sha256(data).hexdigest()
concurrent='306df7bc605477faa7891230879ee609e469805e'
base='a7504eea25f02728d1be6cd0082e8484d639dbe2'
expected={'docs/superpowers/plans/2026-11-15-run19-v06-n4-small-closure-order.md','docs/superpowers/specs/2026-11-15-run19-v06-input-scope.md','docs/superpowers/specs/2026-11-15-run19-v06-n4-checked-contracts.md','verification/run19/planning/v06_n4_publication_20261115/published_math_only.json','verification/run19/planning/v06_n4_publication_20261115/receipt.json'}
actual=set(git('diff','--name-only',base,concurrent).decode().splitlines());assert actual==expected,actual
head=git('rev-parse','HEAD').decode().strip()
for old in [a.publication,concurrent]:subprocess.run(['git','merge-base','--is-ancestor',old,head],cwd=r,check=True)
source=json.loads((r/'verification/run18/runs/v06_alignment_20261115T152000Z_r01/SOURCE_SHA256.json').read_text())
exceptions=expected&set(source)
assert len(exceptions)==2
for name,h in source.items():
 if name not in exceptions:assert sha((r/name).read_bytes())==h,name
for name in expected:assert (r/name).read_bytes()==git('show',concurrent+':'+name),name
code_diff=git('diff','--name-only',a.publication,head,'--','NSP14','NSP14.lean','tests','audit','scripts','lean-toolchain','lakefile.toml','lake-manifest.json').decode().splitlines();assert not code_diff,code_diff
all_diff=set(git('diff','--name-only',a.publication,head).decode().splitlines());assert all_diff==expected,all_diff
for f in ['verification/run18/runs/v06_alignment_20261115T152000Z_r01/MANIFEST_SHA256.json']:
 m=json.loads((r/f).read_text())
 for name,h in m.items():assert sha((r/name).read_bytes())==h,name
report={'status':'PASS_V06_DOC_ONLY_WORK_INTEGRATION','merged_commit':head,'concurrent_work_commit':concurrent,'certified_publication_commit':a.publication,'certified_proof_commit':'d446fc2f18f7a8603d1eedd446e93810dc44d01c','certified_evidence_commit':'0880f6f30836873036b4d9908b7dcef50125d2c8','preserved_concurrent_paths':sorted(expected),'certified_source_files_identical_except_concurrent_run19_docs':len(source)-len(exceptions),'concurrent_existing_source_manifest_exceptions':sorted(exceptions),'no_lean_test_verifier_or_pin_changes':True,'certified_evidence_preserved':True,'certificate_scope':'Fixed proof snapshot d446fc2. This integration preserves independent Run19 planning only; it does not recertify a new mathematical proof or claim Run19 completion. Reproduce full V06 validation by checking out certified_proof_commit.'}
out=r/a.output;out.parent.mkdir(parents=True,exist_ok=False)
with out.open('x') as f:f.write(json.dumps(report,ensure_ascii=False,indent=2)+'\n')
print(json.dumps(report,ensure_ascii=False,indent=2))
