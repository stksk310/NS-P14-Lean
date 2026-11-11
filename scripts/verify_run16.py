#!/usr/bin/env python3
"""Cold, checkout-local verification of all Run16 proofs and inherited regressions."""
from pathlib import Path
import gzip,hashlib,json,re,shutil,subprocess,sys,tempfile,time
root=Path(__file__).resolve().parents[1];out=root/'verification/run16/final';out.mkdir(parents=True,exist_ok=True)
base='447b7ae782414b739968a2a3009dd3a52ae230d0'
def git(*args):return subprocess.check_output(['git',*args],cwd=root)
old=set(git('ls-tree','-r','--name-only',base).decode().splitlines())
sources=sorted(str(p.relative_to(root))for p in (root/'NSP14').rglob('*.lean')if str(p.relative_to(root))not in old)
tests=sorted(str(p.relative_to(root))for p in (root/'tests').glob('*.lean')if str(p.relative_to(root))not in old)
contract='audit/run16/ClosedGoals.lean';new_lean=sources+tests+[contract]
frozen=sorted(p for p in old if (p.startswith(('NSP14/','tests/','audit/'))and p.endswith('.lean'))or p.startswith(('verification/','artifacts/','scripts/'))or p in ['lean-toolchain','lakefile.toml','lake-manifest.json'])
for p in frozen:assert (root/p).read_bytes()==git('show',base+':'+p),p
assert (root/'NSP14.lean').read_text().startswith(git('show',base+':NSP14.lean').decode())
for p in sources:assert 'public import '+p[:-5].replace('/','.')in(root/'NSP14.lean').read_text(),p
for p in new_lean+['NSP14.lean']:
    text=(root/p).read_text()
    assert not re.search(r'\b(?:sorry|admit|sorryAx|native_decide)\b|^\s*(?:private\s+|public\s+)?axiom\b',text,re.M),p
    assert all(x.rstrip()==x for x in text.splitlines()),p
status=json.loads((root/'docs/RUN16_CLOSURE_STATUS.json').read_text())
assert status['proof_goals_complete'] and status['unproved_ids']==[]
def bound_paths():
    return sorted([str(p.relative_to(root))for d in ['NSP14','tests','audit']for p in(root/d).rglob('*.lean')]+['NSP14.lean','lean-toolchain','lakefile.toml','lake-manifest.json','scripts/verify_run16.py','scripts/check_run16_coordinates.py'])
initial={p:hashlib.sha256((root/p).read_bytes()).hexdigest()for p in bound_paths()};records=[]
def run(name,command,compressed=False):
    start=time.monotonic();r=subprocess.run(command,cwd=root,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
    data=r.stdout.encode();(out/(name+('.log.gz'if compressed else'.log'))).write_bytes(gzip.compress(data,mtime=0)if compressed else data)
    records.append(dict(name=name,command=command,exit_code=r.returncode,seconds=round(time.monotonic()-start,3)))
    print(name,r.returncode,flush=True)
    if r.returncode or re.search(r'\bwarning:',r.stdout):print(r.stdout[:12000]);raise SystemExit(r.returncode or 1)
    return r.stdout
fresh='--fresh-test-cache'in sys.argv
if fresh:
    cache=root/'.lake/build/lib/lean/tests';backup=Path(tempfile.mkdtemp(prefix='nsp14-run16-testcache-'))/'tests'
    if cache.exists():shutil.move(str(cache),str(backup))
    cache.mkdir(parents=True,exist_ok=True)
    (out/'fresh_test_cache.json').write_text(json.dumps(dict(mode='empty_project_test_cache',backup=str(backup)),indent=2)+'\n')
run('build',['lake','build','NSP14','Mathlib.Algebra.Field.ZMod','Mathlib.FieldTheory.RatFunc.Basic'])
previous=json.loads((root/'verification/run15_closure/verification.json').read_text());paths=[];other=[]
for check in previous['checks']:
    command=check['command']
    if command[:3]==['lake','env','lean']:
        if check['name']!='environment_axioms'and command[3]not in paths:paths.append(command[3])
    elif check['name']!='build':other.append(command)
for p in sorted((root/'tests').glob('*.lean')):
    rel=str(p.relative_to(root))
    if rel not in paths:paths.append(rel)
paths.append(contract);ordered=[];active=set()
def emit(path):
    if path in ordered:return
    assert path not in active,('fixture cycle',path)
    active.add(path)
    for mod in re.findall(r'^\s*(?:public\s+)?import\s+((?:tests|audit)\.[\w.]+)',(root/path).read_text(),re.M):emit(mod.replace('.','/')+'.lean')
    active.remove(path);ordered.append(path)
for path in paths:emit(path)
for i,path in enumerate(ordered):
    target=root/'.lake/build/lib/lean'/Path(path).with_suffix('.olean');target.parent.mkdir(parents=True,exist_ok=True)
    run('acceptance_'+str(i).zfill(3)+'_'+Path(path).stem,['lake','env','lean',path,'-o',str(target)])
for i,cmd in enumerate(other):run('inherited_numeric_'+str(i),cmd)
run('coordinate_model',['python3','scripts/check_run16_coordinates.py'])
modules=[p[:-5].replace('/','.')for p in ordered];newmodules=[p[:-5].replace('/','.')for p in new_lean]+['NSP14']
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
raw=run('environment_axioms',['lake','env','lean','verification/run16/final/EnvironmentAudit.lean'],True)
declarations=[json.loads(line)for line in raw.splitlines()if line.startswith('{')]
allowed={'propext','Classical.choice','Quot.sound'}
assert declarations and len({d['name']for d in declarations})==len(declarations)
for d in declarations:
    assert set(d['axioms'])<=allowed,(d['name'],d['axioms'])
    assert d['name']not in d['axioms'],d['name']
    d['source']=d['module'].replace('.','/')+'.lean'
    d['source_sha256']=hashlib.sha256((root/d['source']).read_bytes()).hexdigest()
    d['kind']='exported_proof_stub'if d['exported_kind']=='axiom'else d['exported_kind']
newdecls=[d for d in declarations if d['source']in new_lean]
assert set(new_lean)<={d['source']for d in newdecls}
assert all('type'in d and'explicit_type'in d for d in newdecls)
ids=['I_NORMALIZE','E_CORE','E_COORD','E_KERNEL','E_STOP','E_BOUNDS','E_HOMOLOGY','E_TRANSFER','E_ARTIN','E_ROW','E_TWO']
assert {'Run16Closed.'+n for n in ids}<={d['name']for d in newdecls}
assert 'Run15Closed.all_original_goals_closed'in{d['name']for d in declarations}
assert set(bound_paths())==set(initial),'source set changed during verification'
for p,h in initial.items():assert hashlib.sha256((root/p).read_bytes()).hexdigest()==h,('source changed',p)
(out/'declarations.json.gz').write_bytes(gzip.compress((json.dumps(sorted(declarations,key=lambda d:d['name']),ensure_ascii=False,indent=2)+'\n').encode(),mtime=0))
(out/'SOURCE_SHA256.json').write_text(json.dumps(initial,indent=2)+'\n')
summary=dict(status='PASS_RUN16_PROOF_CLOSURE',baseline_commit=base,fresh_project_test_cache=fresh,
    checks=records,fixture_order=ordered,sources=sources,acceptance_tests=tests,closure_contract=contract,
    environment_declarations=len(declarations),new_environment_declarations=len(newdecls),
    frozen_source_dependency_script_and_evidence_count=len(frozen),allowed_axioms=sorted(allowed),
    core_line_count=sum(len((root/p).read_text().splitlines())for p in sources),closed_ids=ids,
    types='all new declarations including instances, constructors and generated helpers: normal and explicit types, source hash')
(out/'verification.json').write_text(json.dumps(summary,ensure_ascii=False,indent=2)+'\n')
manifest={str(p.relative_to(root)):hashlib.sha256(p.read_bytes()).hexdigest()for p in sorted(out.iterdir())if p.is_file()and p.name!='MANIFEST_SHA256.json'}
(out/'MANIFEST_SHA256.json').write_text(json.dumps(manifest,indent=2)+'\n')
print(summary['status'],len(records),'commands',len(declarations),'environment declarations',len(newdecls),'new',flush=True)
