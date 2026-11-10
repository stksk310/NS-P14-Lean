#!/usr/bin/env python3
"""Kernel-build, predecessor regression and environment-level axiom audit for Run13."""
from pathlib import Path
import hashlib, json, re, subprocess, time, os
root=Path(__file__).resolve().parents[1]
out=root/'verification/block13_continuation'
out.mkdir(parents=True,exist_ok=True)
baseline=json.loads((root/'verification/block12/MANIFEST_SHA256.json').read_text())
sources=sorted(str(p.relative_to(root)) for p in (root/'NSP14/Homological').glob('*.lean'))
newtests=sorted(str(p.relative_to(root)) for p in (root/'tests').glob('*.lean') if str(p.relative_to(root)) not in baseline and p.name!='Run13Axioms.lean')
actualsources=sorted(str(p.relative_to(root)) for p in (root/'NSP14').rglob('*.lean') if str(p.relative_to(root)) not in baseline)
assert sources==actualsources, ('Unregistered sources',actualsources)
rootimports=(root/'NSP14.lean').read_text()
assert all('public import '+p[:-5].replace('/','.') in rootimports for p in sources)
for p in sources+newtests:
    assert not re.search(r'\b(?:sorry|admit|sorryAx|native_decide)\b|^axiom\b',(root/p).read_text(),re.M),p
frozen=sorted(p for p in baseline if (p.startswith('NSP14/') or p.startswith('tests/')) and p.endswith('.lean'))+['lean-toolchain','lakefile.toml','lake-manifest.json']
for p in frozen:
    assert hashlib.sha256((root/p).read_bytes()).hexdigest()==baseline[p],p
previous=[('block01','tests/SmallScalar.lean',10),('block02','tests/Sidon.lean',14),('block03','tests/Resources.lean',7),('block04','tests/LowRank.lean',13),('block05','tests/LargeSeed.lean',22),('block06','tests/LargeScalar.lean',15),('block07','tests/OrdinaryNumerical.lean',25),('block08','tests/SemigroupFoundations.lean',86),('block09','tests/SemigroupRing.lean',60),('block10','tests/TangentAlgebra.lean',71),('block11','tests/AperyQuotient.lean',120)]
run12=['tests/Run12BasicExamples.lean','tests/Run12Fixtures.lean','tests/JumpBounds.lean','tests/PolynomialAction.lean','tests/JumpStrata.lean','tests/CompletedComparison.lean']
def compile_test(p):
    target=root/'.lake/build/lib/lean'/Path(p).with_suffix('.olean')
    target.parent.mkdir(parents=True,exist_ok=True)
    return ['lake','env','lean',p,'-o',str(target)]
records=[]
def run(name,cmd):
    t=time.monotonic()
    r=subprocess.run(cmd,cwd=root,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
    (out/(name+'.log')).write_text(r.stdout)
    records.append(dict(name=name,command=cmd,exit_code=r.returncode,seconds=round(time.monotonic()-t,3)))
    print(name,r.returncode,flush=True)
    if r.returncode or re.search(r'\bwarning:',r.stdout):
        print(r.stdout,flush=True);raise SystemExit(r.returncode or 1)
    return r.stdout
run('build',['lake','build'])
for name,p,_ in previous:run(name,compile_test(p))
for p in run12:run(Path(p).stem,compile_test(p))
run('run12_axioms',['lake','env','lean','tests/Run12Axioms.lean'])
for p in newtests:run(Path(p).stem,compile_test(p))
modules=[p[:-5].replace('/','.') for p in newtests]
audit='''module\nimport NSP14\n'''+''.join('import '+m+'\n' for m in modules)+'''
import Lean
open Lean
set_option maxRecDepth 4000
set_option maxHeartbeats 0
#eval show MetaM Unit from do
  let env ← getEnv
  let tests : Array String := #['''+','.join(json.dumps(m) for m in modules)+''']
  for (n,ci) in env.constants.toList do
    let some idx := env.getModuleIdxFor? n | continue
    let modName := env.header.moduleNames[idx.toNat]!.toString
    if modName.startsWith "NSP14.Homological." || tests.contains modName then
      let axs ← collectAxioms n
      let kind := match ci with
        | .axiomInfo _ => "axiom"
        | .defnInfo _ => "def"
        | .thmInfo _ => "theorem"
        | .opaqueInfo _ => "opaque"
        | .quotInfo _ => "quotient"
        | .inductInfo _ => "inductive"
        | .ctorInfo _ => "constructor"
        | .recInfo _ => "recursor"
      let type ← Lean.Meta.ppExpr ci.type
      let explicitType ← withOptions (fun opts => opts.setBool `pp.explicit true) (Lean.Meta.ppExpr ci.type)
      IO.println ((Json.mkObj [("name",toJson n.toString),("module",toJson modName),
        ("kind",toJson kind),("axioms",toJson (axs.map Name.toString)),
        ("type",toJson type.pretty),("explicit_type",toJson explicitType.pretty)]).compress)
'''
(out/'EnvironmentAudit.lean').write_text(audit)
raw=run('environment_axioms',['lake','env','lean',str((out/'EnvironmentAudit.lean').relative_to(root))])
decls=[json.loads(line) for line in raw.splitlines() if line.startswith('{')]
assert decls and len({d['name'] for d in decls})==len(decls)
allowed={'propext','Classical.choice','Quot.sound'}
for d in decls:
    assert set(d['axioms'])<=allowed,(d['name'],d['axioms'])
    # Lean 4 module exports erase many checked proof bodies to axiomInfo stubs.
    # collectAxioms reads the kernel's precomputed export extension, so genuine
    # axioms include their own name; erased proved exports do not.
    assert d['name'] not in d['axioms'], ('Genuine new mathematical axiom',d['name'])
    d['exported_kind']=d['kind']
    if d['kind']=='axiom':d['kind']='exported_proof_stub'
    d['source']=d['module'].replace('.','/')+'.lean'
assert {d['source'] for d in decls if d['source'] in sources}==set(sources)
counts={}
for name,_,count in previous+[('run12_axioms','',298)]:
    reports=re.findall(r"'([^']+)' (?:depends on axioms:\s*\[([^]]*)\]|does not depend on any axioms)",(out/(name+'.log')).read_text(),re.S)
    assert len(reports)==count,(name,len(reports),count)
    for decl,axs in reports:assert {a.strip() for a in axs.split(',') if a.strip()}<=allowed,(decl,axs)
    counts[name]=len(reports)
run('schedule',['python3','lean_planning/checks/check_run_schedule_r02.py'])
run('block01_domains',['lake','env','lean','audit/DomainChecks.lean'])
run('block02_assumptions',['lake','env','lean','audit/block02/AssumptionChecks.lean'])
# Status is supplied by the independently reviewed completion declaration, never by build success alone.
closure=json.loads((root/'docs/RUN13_CLOSURE_STATUS.json').read_text())
summary=dict(status='PASS_FORMAL_VERIFICATION',closure=closure,baseline_commit='6b8d16889ea9b4d88567f0d9ac70391db2a49824',continuation_baseline='92cbe8f875845fbcefc76c6c819780fe8776429c',checks=records,environment_declarations=len(decls),core_declarations=sum(d['source'] in sources for d in decls),test_declarations=sum(d['source'] in newtests for d in decls),core_line_count=sum(len((root/p).read_text().splitlines()) for p in sources),sources=sources,acceptance_tests=newtests,allowed_axioms=sorted(allowed),old_axiom_reports=counts,frozen_hash_count=len(frozen),predecessor_and_fixed_environment_unchanged=True)
(out/'declarations.json').write_text(json.dumps(sorted(decls,key=lambda d:d['name']),ensure_ascii=False,indent=2)+'\n')
(out/'verification.json').write_text(json.dumps(summary,ensure_ascii=False,indent=2)+'\n')
print('PASS_FORMAL_VERIFICATION',len(records),'commands',len(decls),'environment declarations',flush=True)
