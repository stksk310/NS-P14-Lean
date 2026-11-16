#!/usr/bin/env python3
"""Verify the partial Run14 exports; build success does not certify Run14 closure."""
from pathlib import Path
import hashlib,json,re,subprocess,time,os
root=Path(__file__).resolve().parents[1]
out=root/'verification/run14';out.mkdir(parents=True,exist_ok=True)
base='d8556dc615b1e1633379f4567e9e795b3f1c8ae3'
def git(*a):return subprocess.check_output(['git',*a],cwd=root)
old=set(git('ls-tree','-r','--name-only',base).decode().splitlines())
sources=sorted(str(p.relative_to(root)) for p in (root/'NSP14').rglob('*.lean') if str(p.relative_to(root)) not in old)
tests=sorted(str(p.relative_to(root)) for p in (root/'tests').glob('*.lean') if str(p.relative_to(root)) not in old)
assert sources and tests
rootimports=(root/'NSP14.lean').read_text()
assert rootimports.startswith(git('show',base+':NSP14.lean').decode())
assert all('public import '+p[:-5].replace('/','.') in rootimports for p in sources)
frozen=sorted(p for p in old if ((p.startswith('NSP14/') or p.startswith('tests/')) and p.endswith('.lean')) or p in ['lean-toolchain','lakefile.toml','lake-manifest.json'])
for p in frozen:assert (root/p).read_bytes()==git('show',base+':'+p),p
for p in sources+tests+['NSP14.lean','audit/run14/RemainingGoals.lean']:
 assert not re.search(r'\b(?:sorry|admit|sorryAx|native_decide)\b|^\s*(?:private\s+|public\s+)?axiom\b',(root/p).read_text(),re.M),p
records=[]
def run(name,cmd):
 t=time.monotonic();r=subprocess.run(cmd,cwd=root,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
 (out/(name+'.log')).write_text(r.stdout)
 records.append(dict(name=name,command=cmd,exit_code=r.returncode,seconds=round(time.monotonic()-t,3)))
 print(name,r.returncode,flush=True)
 if r.returncode or re.search(r'\bwarning:',r.stdout):print(r.stdout);raise SystemExit(r.returncode or 1)
 return r.stdout
def compile_test(p):
 target=root/'.lake/build/lib/lean'/Path(p).with_suffix('.olean');target.parent.mkdir(parents=True,exist_ok=True)
 return ['lake','env','lean',p,'-o',str(target)]
run('build',['lake','build'])
# Preserve fixture dependency order. Every old test included in the Run13 full suite is rerun.
oldchecks=[p['command'] for p in json.loads((root/'verification/block13_continuation/verification.json').read_text())['checks']
 if p['name'] not in ['build','environment_axioms']]
for i,cmd in enumerate(oldchecks):run('predecessor_'+str(i).zfill(2),cmd)
ordered=['tests/Run14Fixtures.lean']+[p for p in tests if p!='tests/Run14Fixtures.lean']
for p in ordered:run(Path(p).stem,compile_test(p))
run('remaining_goal_types',['lake','env','lean','audit/run14/RemainingGoals.lean'])
modules=[p[:-5].replace('/','.') for p in ordered]
audit='''module
import NSP14
'''+''.join('import '+m+'\n' for m in modules)+'''import Lean
open Lean
set_option maxRecDepth 4000
set_option maxHeartbeats 0
#eval show MetaM Unit from do
 let env ← getEnv
 let included : Array String := #['''+','.join(json.dumps(m) for m in modules)+''']
 for (n,ci) in env.constants.toList do
  let some idx := env.getModuleIdxFor? n | continue
  let modName := env.header.moduleNames[idx.toNat]!.toString
  if modName == "NSP14" || modName.startsWith "NSP14." || included.contains modName then
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
raw=run('environment_axioms',['lake','env','lean','verification/run14/EnvironmentAudit.lean'])
decls=[json.loads(l) for l in raw.splitlines() if l.startswith('{')]
allowed={'propext','Classical.choice','Quot.sound'}
assert decls and len({d['name'] for d in decls})==len(decls)
for d in decls:
 assert set(d['axioms'])<=allowed,(d['name'],d['axioms'])
 assert d['name'] not in d['axioms'],d['name']
 d['exported_kind']=d['kind']
 if d['kind']=='axiom':d['kind']='exported_proof_stub'
 d['source']=d['module'].replace('.','/')+'.lean'
assert set(sources)<={d['source'] for d in decls}
newdecls=[d for d in decls if d['source'] in sources+tests]
status=json.loads((root/'docs/RUN14_CLOSURE_STATUS.json').read_text())
assert status['status']=='PARTIAL_NOT_RUN14_COMPLETE'
summary=dict(status='PASS_IMPLEMENTED_EXPORTS_ONLY',closure=status,baseline_commit=base,
 checks=records,sources=sources,acceptance_tests=ordered,environment_declarations=len(decls),
 new_environment_declarations=len(newdecls),frozen_source_and_dependency_count=len(frozen),
 allowed_axioms=sorted(allowed),core_line_count=sum(len((root/p).read_text().splitlines()) for p in sources))
(out/'declarations.json').write_text(json.dumps(sorted(decls,key=lambda d:d['name']),ensure_ascii=False,indent=2)+'\n')
(out/'verification.json').write_text(json.dumps(summary,ensure_ascii=False,indent=2)+'\n')
paths=sources+tests+['NSP14.lean','audit/run14/RemainingGoals.lean','lean-toolchain','lakefile.toml','lake-manifest.json','scripts/verify_run14.py','docs/RUN14_CLOSURE_STATUS.json']
(out/'SOURCE_SHA256.json').write_text(json.dumps({p:hashlib.sha256((root/p).read_bytes()).hexdigest() for p in paths},indent=2)+'\n')
print('PASS_IMPLEMENTED_EXPORTS_ONLY',len(records),'commands',len(decls),'all project declarations',len(newdecls),'new declarations',flush=True)
