#!/usr/bin/env python3
"""Verify proved Run15 exports only. A green run never certifies Run15 closure."""
from pathlib import Path
import gzip, hashlib, json, re, shutil, subprocess, sys, tempfile, time
root=Path(__file__).resolve().parents[1]
out=root/'verification/run15_bclosure';out.mkdir(parents=True,exist_ok=True)
source_base='ecbbf334479e1d91572cfd75914abaf8015d371e'
base='ecbbf334479e1d91572cfd75914abaf8015d371e'
def git(*args): return subprocess.check_output(['git',*args],cwd=root)
old=set(git('ls-tree','-r','--name-only',base).decode().splitlines())
sources=sorted(str(p.relative_to(root)) for p in (root/'NSP14').rglob('*.lean') if str(p.relative_to(root)) not in old)
tests=sorted(str(p.relative_to(root)) for p in (root/'tests').glob('*.lean') if str(p.relative_to(root)) not in old)
remaining='audit/run15_bclosure/ClosedGoals.lean'
assert sources and tests
rootimports=(root/'NSP14.lean').read_text()
assert rootimports.startswith(git('show',base+':NSP14.lean').decode())
assert all('public import '+p[:-5].replace('/','.') in rootimports for p in sources)
frozen=sorted(p for p in old if (p.startswith(('NSP14/','tests/','audit/')) and p.endswith('.lean'))
              or p.startswith(('verification/','artifacts/','scripts/'))
              or p in ['lean-toolchain','lakefile.toml','lake-manifest.json'])
for p in frozen: assert (root/p).read_bytes()==git('show',base+':'+p),p
for p in sources+tests+[remaining,'NSP14.lean']:
    assert not re.search(r'\b(?:sorry|admit|sorryAx|native_decide)\b|^\s*(?:private\s+|public\s+)?axiom\b',(root/p).read_text(),re.M),p
    assert all(line.rstrip()==line for line in (root/p).read_text().splitlines()),p
for p in sources: assert 'Run15Remaining' not in (root/p).read_text(),p
status=json.loads((root/'docs/RUN15_CLOSURE_STATUS.json').read_text())
assert status['status']=='PARTIAL_NOT_RUN15_COMPLETE' and status['run15_complete'] is False
records=[]
def run(name,command,compressed=False):
    start=time.monotonic()
    result=subprocess.run(command,cwd=root,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
    data=result.stdout.encode()
    if compressed:(out/(name+'.log.gz')).write_bytes(gzip.compress(data,mtime=0))
    else:(out/(name+'.log')).write_bytes(data)
    records.append(dict(name=name,command=command,exit_code=result.returncode,seconds=round(time.monotonic()-start,3)))
    print(name,result.returncode,flush=True)
    if result.returncode or re.search(r'\bwarning:',result.stdout):
        print(result.stdout[:16000],flush=True);raise SystemExit(result.returncode or 1)
    return result.stdout

def compile_lean(path):
    # Never replay an absolute -o from a previous checkout (Run14-P2 repair).
    target=root/'.lake/build/lib/lean'/Path(path).with_suffix('.olean')
    target.parent.mkdir(parents=True,exist_ok=True)
    return ['lake','env','lean',path,'-o',str(target)]

fresh='--fresh-test-cache' in sys.argv
if fresh:
    cache=root/'.lake/build/lib/lean/tests'
    backup=Path(tempfile.mkdtemp(prefix='nsp14-run15-testcache-'))/'tests'
    if cache.exists():shutil.move(str(cache),str(backup))
    cache.mkdir(parents=True,exist_ok=True)
    (out/'fresh_test_cache.json').write_text(json.dumps(dict(mode='empty_project_test_cache',backup=str(backup)),indent=2)+'\n')
run('build',['lake','build','NSP14','Mathlib.Algebra.Field.ZMod','Mathlib.FieldTheory.RatFunc.Basic'])
previous=json.loads((root/'verification/run14_reproducibility_fix/verification.json').read_text())
oldchecks=[c['command'] for c in previous['checks'] if c['name'] not in ['build','environment_axioms']]
leanpaths=[];other=[]
for command in oldchecks:
    if command[:3]==['lake','env','lean']:
        if command[3] not in leanpaths:leanpaths.append(command[3])
    else:other.append(command)
# Every project acceptance file, including previously omitted Run13Axioms.
for p in sorted((root/'tests').glob('*.lean')):
    rel=str(p.relative_to(root))
    if rel not in leanpaths:leanpaths.append(rel)
leanpaths.append(remaining)
ordered=[];active=set()
def emit(path):
    if path in ordered:return
    assert path not in active,('cyclic Lean fixture imports',path)
    active.add(path)
    imports=re.findall(r'^\s*(?:public\s+)?import\s+((?:tests|audit)\.[\w.]+)',(root/path).read_text(),re.M)
    for module in imports:
        dep=module.replace('.','/')+'.lean'
        assert (root/dep).is_file(),(path,dep)
        emit(dep)
    active.remove(path);ordered.append(path)
for p in leanpaths:emit(p)
for i,p in enumerate(ordered):run('acceptance_'+str(i).zfill(2)+'_'+Path(p).stem,compile_lean(p))
for i,command in enumerate(other):run('numeric_regression_'+str(i),command)
modules=[p[:-5].replace('/','.') for p in ordered]
newmodules=[p[:-5].replace('/','.') for p in sources+tests+[remaining]]
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
raw=run('environment_axioms',['lake','env','lean','verification/run15_bclosure/EnvironmentAudit.lean'],True)
declarations=[json.loads(line) for line in raw.splitlines() if line.startswith('{')]
allowed={'propext','Classical.choice','Quot.sound'}
assert declarations and len({d['name'] for d in declarations})==len(declarations)
for d in declarations:
    assert set(d['axioms'])<=allowed,(d['name'],d['axioms'])
    assert d['name'] not in d['axioms'],d['name']
    d['source']=d['module'].replace('.','/')+'.lean'
    # Imported proof-erased exported declarations can have axiomInfo but
    # collectAxioms remains the authoritative transitive kernel dependency check.
    d['kind']='exported_proof_stub' if d['exported_kind']=='axiom' else d['exported_kind']
newdecls=[d for d in declarations if d['source'] in sources+tests+[remaining]]
assert set(sources+tests+[remaining])<={d['source'] for d in newdecls}
assert all('explicit_type' in d for d in newdecls)
assert 'Run15BClosure.actual_tor_to_row_closed' in {d['name'] for d in newdecls}
summary=dict(status='PASS_IMPLEMENTED_EXPORTS_ONLY_NOT_RUN15_COMPLETE',baseline_commit=base,source_baseline_commit=source_base,
    fresh_project_test_cache=fresh,fixture_order=ordered,checks=records,sources=sources,acceptance_tests=tests,
    environment_declarations=len(declarations),new_environment_declarations=len(newdecls),
    frozen_source_dependency_script_and_evidence_count=len(frozen),allowed_axioms=sorted(allowed),
    core_line_count=sum(len((root/p).read_text().splitlines()) for p in sources),
    exact_original_actual_tor_to_row_goal_proof=remaining,run15_complete=False,
    types='declarations.json.gz: normal and explicit types for all new declarations, instances, constructors, helpers and goal definitions')
(out/'declarations.json.gz').write_bytes(gzip.compress((json.dumps(sorted(declarations,key=lambda d:d['name']),ensure_ascii=False,indent=2)+'\n').encode(),mtime=0))
(out/'verification.json').write_text(json.dumps(summary,ensure_ascii=False,indent=2)+'\n')
paths=sources+tests+[remaining,'NSP14.lean','lean-toolchain','lakefile.toml','lake-manifest.json','scripts/verify_run15_bclosure.py','docs/RUN15_CLOSURE_STATUS.json']
(out/'SOURCE_SHA256.json').write_text(json.dumps({p:hashlib.sha256((root/p).read_bytes()).hexdigest() for p in paths},indent=2)+'\n')
print(summary['status'],len(records),'commands',len(declarations),'all project declarations',len(newdecls),'new declarations',flush=True)
