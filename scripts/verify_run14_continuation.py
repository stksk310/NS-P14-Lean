#!/usr/bin/env python3
"""Run14 closure: frozen predecessors, kernel regression, full environment axiom audit."""
from pathlib import Path
import gzip, hashlib, json, re, subprocess, time, sys, shutil, tempfile
root=Path(__file__).resolve().parents[1]
out=root/'verification/run14_continuation';out.mkdir(parents=True,exist_ok=True)
base='8040c90138bf1aa76cc99d9a5e7df7b2c1a8a206'
repair='aa6bf4ced7ea308686066e377ba1e5bc992a098e'
def git(*a):return subprocess.check_output(['git',*a],cwd=root)
old=set(git('ls-tree','-r','--name-only',base).decode().splitlines())
sources=sorted(str(p.relative_to(root)) for p in (root/'NSP14').rglob('*.lean') if str(p.relative_to(root)) not in old)
tests=sorted(str(p.relative_to(root)) for p in (root/'tests').glob('*.lean') if str(p.relative_to(root)) not in old)
closed='audit/run14_continuation/ClosedGoals.lean'
rootimports=(root/'NSP14.lean').read_text()
assert rootimports.startswith(git('show',base+':NSP14.lean').decode())
assert all('public import '+p[:-5].replace('/','.') in rootimports for p in sources)
frozen=sorted(p for p in old if ((p.startswith('NSP14/') or p.startswith('tests/')) and p.endswith('.lean')) or p in ['lean-toolchain','lakefile.toml','lake-manifest.json','audit/run14/RemainingGoals.lean'] or p.startswith('verification/run14/') or p.startswith('artifacts/NS_P14_LEAN_RUN14_PARTIAL_'))
for p in frozen:assert (root/p).read_bytes()==git('show',base+':'+p),p
repairpaths=git('diff','--name-only',base,repair).decode().splitlines()
assert all(p=='scripts/verify_run13_continuation.py' or p.startswith('verification/block13_reproducibility_fix/') for p in repairpaths)
for p in repairpaths:assert (root/p).read_bytes()==git('show',repair+':'+p),p
for p in sources+tests+[closed,'NSP14.lean']:
 assert not re.search(r'\b(?:sorry|admit|sorryAx|native_decide)\b|^\s*(?:private\s+|public\s+)?axiom\b',(root/p).read_text(),re.M),p
records=[]
def run(name,cmd,compressed=False):
 t=time.monotonic();r=subprocess.run(cmd,cwd=root,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
 data=r.stdout.encode()
 if compressed:(out/(name+'.log.gz')).write_bytes(gzip.compress(data,mtime=0))
 else:(out/(name+'.log')).write_bytes(data)
 records.append(dict(name=name,command=cmd,exit_code=r.returncode,seconds=round(time.monotonic()-t,3)))
 print(name,r.returncode,flush=True)
 if r.returncode or re.search(r'\bwarning:',r.stdout):print(r.stdout[:15000]);raise SystemExit(r.returncode or 1)
 return r.stdout
def compile_test(p):
 target=root/'.lake/build/lib/lean'/Path(p).with_suffix('.olean');target.parent.mkdir(parents=True,exist_ok=True)
 return ['lake','env','lean',p,'-o',str(target)]
fresh_cache='--fresh-test-cache' in sys.argv
if fresh_cache:
 cache=root/'.lake/build/lib/lean/tests'
 backup=Path(tempfile.mkdtemp(prefix='nsp14-run14-testcache-'))/'tests'
 if cache.exists():shutil.move(str(cache),str(backup))
 cache.mkdir(parents=True,exist_ok=True)
 (out/'fresh_test_cache.json').write_text(json.dumps(dict(mode='empty_project_test_cache',backup=str(backup)),indent=2)+'\n')
run('build',['lake','build','NSP14','Mathlib.Algebra.Field.ZMod','Mathlib.FieldTheory.RatFunc.Basic'])
oldchecks=[p['command'] for p in json.loads((root/'verification/run14/verification.json').read_text())['checks'] if p['name'] not in ['build','environment_axioms']]
# Read the actual fixture imports rather than inheriting the pre-repair cached order.
path_index={c[3]:i for i,c in enumerate(oldchecks) if c[:3]==['lake','env','lean']}
prerequisites={}
for p,i in path_index.items():
 imports=re.findall(r'^\s*(?:public\s+)?import\s+(tests\.[\w.]+)',(root/p).read_text(),re.M)
 prerequisites[i]=[path_index[m.replace('.','/')+'.lean'] for m in imports if m.replace('.','/')+'.lean' in path_index]
ordered=[];active=set()
def emit(i):
 if i in ordered:return
 assert i not in active,('cyclic fixture imports',i)
 active.add(i)
 for j in prerequisites.get(i,[]):emit(j)
 active.remove(i);ordered.append(i)
for i in range(len(oldchecks)):emit(i)
for i in ordered:run('predecessor_'+str(i).zfill(2),oldchecks[i])

for p in tests:run(Path(p).stem,compile_test(p))
run('historical_goal_types',compile_test('audit/run14/RemainingGoals.lean'))
run('closed_historical_goals',compile_test(closed))
modules=[p[:-5].replace('/','.') for p in tests+[closed]]
newmodules=[p[:-5].replace('/','.') for p in sources+tests+[closed]]
audit='''module
import NSP14
'''+''.join('import '+m+'\n' for m in modules)+'''import Lean
open Lean
set_option maxRecDepth 4000
set_option maxHeartbeats 0
#eval show MetaM Unit from do
 let env ← getEnv
 let included : Array String := #['''+','.join(json.dumps(m) for m in modules)+''']
 let newModules : Array String := #['''+','.join(json.dumps(m) for m in newmodules)+''']
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
   let mut fields := [("name",toJson n.toString),("module",toJson modName),
    ("exported_kind",toJson kind),("axioms",toJson (axs.map Name.toString))]
   if newModules.contains modName then
    let type ← Lean.Meta.ppExpr ci.type
    let explicitType ← withOptions (fun opts => opts.setBool `pp.explicit true) (Lean.Meta.ppExpr ci.type)
    fields := fields ++ [("type",toJson type.pretty),("explicit_type",toJson explicitType.pretty)]
   IO.println ((Json.mkObj fields).compress)
'''
(out/'EnvironmentAudit.lean').write_text(audit)
raw=run('environment_axioms',['lake','env','lean','verification/run14_continuation/EnvironmentAudit.lean'],True)
decls=[json.loads(l) for l in raw.splitlines() if l.startswith('{')]
allowed={'propext','Classical.choice','Quot.sound'}
assert decls and len({d['name'] for d in decls})==len(decls)
for d in decls:
 assert set(d['axioms'])<=allowed,(d['name'],d['axioms'])
 assert d['name'] not in d['axioms'],d['name']
 d['source']=d['module'].replace('.','/')+'.lean'
 d['kind']='exported_proof_stub' if d['exported_kind']=='axiom' else d['exported_kind']
assert set(sources+tests+[closed])<={d['source'] for d in decls}
newdecls=[d for d in decls if d['source'] in sources+tests+[closed]]
assert all('explicit_type' in d for d in newdecls)
status=dict(status='COMPLETE',baseline_commit=base,integrated_remote_commit=repair,run13='COMPLETE_AND_PUSHED',
 goals={n:'COMPLETE' for n in ['1_offset_stabilization_volume','2_green_degree_two','3_same_characteristic_one_cut','4_actual_tower','5_one_resource_sequence','6_actual_numerical_data','7_actual_sidon_boundary','8_actual_all_rows']},
 historical_remaining_types='audit/run14/RemainingGoals.lean (preserved)',
 historical_goal_proofs=closed,next_required_run='RUN15_ACTUAL_TOR_AND_TARGET_BETTI',
 run15_actual_tor_and_target_betti='DEFERRED_AS_REQUESTED',evidence='verification/run14_continuation/verification.json')
(root/'docs/RUN14_CLOSURE_STATUS.json').write_text(json.dumps(status,ensure_ascii=False,indent=2)+'\n')
summary=dict(status='PASS_RUN14_CLOSURE',baseline_commit=base,integrated_remote_commit=repair,frozen_remote_repair_count=len(repairpaths),fresh_project_test_cache=fresh_cache,predecessor_order=ordered,checks=records,sources=sources,acceptance_tests=tests+[closed],
 environment_declarations=len(decls),new_environment_declarations=len(newdecls),frozen_source_dependency_and_evidence_count=len(frozen),
 allowed_axioms=sorted(allowed),core_line_count=sum(len((root/p).read_text().splitlines()) for p in sources),
 types='declarations.json.gz: explicit types for every new environment declaration; frozen old explicit types in verification/run14')
(out/'declarations.json.gz').write_bytes(gzip.compress((json.dumps(sorted(decls,key=lambda d:d['name']),ensure_ascii=False,indent=2)+'\n').encode(),mtime=0))
(out/'verification.json').write_text(json.dumps(summary,ensure_ascii=False,indent=2)+'\n')
paths=sources+tests+[closed,'NSP14.lean','lean-toolchain','lakefile.toml','lake-manifest.json','scripts/verify_run14_continuation.py','docs/RUN14_CLOSURE_STATUS.json']
(out/'SOURCE_SHA256.json').write_text(json.dumps({p:hashlib.sha256((root/p).read_bytes()).hexdigest() for p in paths},indent=2)+'\n')
print('PASS_RUN14_CLOSURE',len(records),'commands',len(decls),'all project declarations',len(newdecls),'new declarations',flush=True)
