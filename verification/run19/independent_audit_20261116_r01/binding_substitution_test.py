from pathlib import Path
import subprocess,tempfile,json,importlib.util,hashlib
repo=Path('/workspace/NS-P14-Lean-run18')
spec=importlib.util.spec_from_file_location('run19_repro_package',repo/'scripts/package_run19_audit.py');pkg=importlib.util.module_from_spec(spec);spec.loader.exec_module(pkg);v=pkg.verify
with tempfile.TemporaryDirectory(prefix='run19-reviewed-source-repro-') as tmp:
 root=Path(tmp)
 def git(*args):return subprocess.check_output(['git',*args],cwd=root,stderr=subprocess.STDOUT).decode().strip()
 def write(name,value):
  p=root/name;p.parent.mkdir(parents=True,exist_ok=True);p.write_text(value)
 def commit(msg):
  git('add','-A');git('-c','user.name=Independent Audit','-c','user.email=audit@example.invalid','commit','-qm',msg);return git('rev-parse','HEAD')
 git('init','-q');write('src.lean','-- certified source A\n');proof=commit('certified source A')
 rel='verification/run19/runs/control';out=root/rel;out.mkdir(parents=True)
 summary=dict(status='PASS_RUN19_COMPLETE_VALIDATION',unproved_ids=[],closed_ids=sorted(v.FULL_IDS),fresh_whole_project_cache=True,
  proof_snapshot_commit=proof,checks=[dict(passed=True,exit_code=0)])
 write(rel+'/verification.json',json.dumps(summary));write(rel+'/SOURCE_SHA256.json',json.dumps(v.source_manifest(root)))
 write(rel+'/MANIFEST_SHA256.json',json.dumps(v.evidence_manifest(root,out)))
 write('src.lean','-- DIFFERENT source B in reviewed commit\n');reviewed=commit('reviewed source B with bound evidence')
 write('src.lean','-- certified source A\n');commit('restore certified source A')
 body='verification/run19/review/body.md';review='verification/run19/review/decision.json'
 write(body,'Synthetic audit control, not a mathematical review.\n')
 decision=dict(verdict='PASS',critical=0,important=0,minor=0,pending=[],declined=[],closed_ids=sorted(v.FULL_IDS),
  source_snapshot_commit=proof,reviewed_commit=reviewed,review_report=body,review_report_sha256=v.sha((root/body).read_bytes()),
  verification_summary_sha256=v.sha((out/'verification.json').read_bytes()),verification_manifest_sha256=v.sha((out/'MANIFEST_SHA256.json').read_bytes()))
 write(review,json.dumps(decision));head=commit('publication review')
 expected=v.sha((root/'src.lean').read_bytes());reviewed_sha=hashlib.sha256(v.git(root,'show',reviewed+':src.lean')).hexdigest();assert expected!=reviewed_sha
 try:
  payload,binding=pkg.checked_payload(root,rel,review);accepted=True;reason=None
 except Exception as e:accepted=False;reason=repr(e)
 result=dict(status='REPRODUCED_REVIEWED_SOURCE_GIT_BINDING_GAP'if accepted else'REJECTED',accepted=accepted,proof=proof,reviewed_commit=reviewed,head=head,
  certified_source_sha256=expected,reviewed_source_sha256=reviewed_sha,reviewed_source_differs=True,rejection=reason,
  scope='Disposable synthetic publication control; no repository source or published evidence modified.')
 print(json.dumps(result,indent=2))
 Path('/tmp/run19_reviewed_source_binding_red.json').write_text(json.dumps(result,indent=2)+'\n')
 assert not accepted, 'reviewed_source_git_substitution: invalid input accepted'
 assert reason and 'reviewed source Git bytes mismatch' in reason, reason
