#!/usr/bin/env python3
"""Validate the honest Run18 partial snapshot, preserving all inherited evidence."""
from pathlib import Path
import argparse,datetime,gzip,hashlib,json,re,shutil,subprocess,tempfile,time,uuid
ROOT=Path(__file__).resolve().parents[1]
BASE='c4fd8153f55bb231aab4168a47c1546888fa7ab0'
FROZEN='86a0a18eff0632cb915d67748dcef47a88991cebf287ef95750f58b450bea689'
ALLOWED={'propext','Classical.choice','Quot.sound'}
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def git(*args):return subprocess.check_output(['git',*args],cwd=ROOT)
def validated_kind(declaration):
    # Lean's public module interface can expose a proved theorem as axiomInfo.
    # The recorded transitive dependencies distinguish it from an actual axiom.
    forbidden=set(declaration['axioms'])-ALLOWED
    if forbidden or declaration['name']in declaration['axioms']:
        raise ValueError('unapproved mathematical axiom dependency: '+declaration['name'])
    return 'exported_proof_stub'if declaration['kind']=='axiom'else declaration['kind']

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--fresh-test-cache',action='store_true')
    parser.add_argument('--output-dir')
    args=parser.parse_args()
    stamp=datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%SZ')
    rel=Path(args.output_dir or f'verification/run18/runs/check_{stamp}_{uuid.uuid4().hex[:8]}')
    if rel.is_absolute()or'..'in rel.parts or rel.parts[:3]!=('verification','run18','runs'):parser.error('new directory under verification/run18/runs required')
    out=ROOT/rel
    if out.exists():parser.error('output exists; inherited evidence is immutable')
    out.mkdir(parents=True,exist_ok=False)
    print('EVIDENCE_DIRECTORY',rel.as_posix(),flush=True)
    old=set(git('ls-tree','-r','--name-only',BASE).decode().splitlines())
    append_only={'NSP14.lean','LEAN_PROGRESS.md','docs/LEAN_PAPER_ALIGNMENT_JA.md'}
    for f in sorted(old-append_only):assert(ROOT/f).read_bytes()==git('show',BASE+':'+f),('inherited bytes changed',f)
    for f in append_only:assert(ROOT/f).read_bytes().startswith(git('show',BASE+':'+f)),f
    retained={str(p.relative_to(ROOT)):sha(p)for d in ['verification','artifacts']for p in(ROOT/d).rglob('*')if p.is_file()and not p.is_relative_to(out)}
    new_sources=sorted(str(p.relative_to(ROOT))for d in ['NSP14','tests','audit/run18']for p in(ROOT/d).rglob('*.lean')if str(p.relative_to(ROOT))not in old)
    open_acceptances=[f for f in new_sources if '/acceptance/'in f and Path(f).stem!='W_FIVE']
    valid_new=[f for f in new_sources if f not in open_acceptances]
    bound=sorted([str(p.relative_to(ROOT))for d in ['NSP14','tests','audit']for p in(ROOT/d).rglob('*.lean')]+[
        'NSP14.lean','lean-toolchain','lakefile.toml','lake-manifest.json','scripts/verify_run18.py',
        'scripts/check_run18_width.py','scripts/check_run18_continuation.py','scripts/check_run18_five.py','scripts/package_run18_audit.py','scripts/check_run18_guards.py','scripts/check_run18_axiom_policy.py',
        'docs/RUN18_INPUT_INVENTORY_JA.md','docs/RUN18_PAPER_CORRESPONDENCE_JA.md',
        'docs/superpowers/plans/2026-11-13-run18-lex-width-closure-order.md']+
        [str(p.relative_to(ROOT))for p in(ROOT/'verification/run18/acceptance_probes_20261113').iterdir()if p.is_file()]+
        [str(p.relative_to(ROOT))for p in(ROOT/'verification/run18/runs/release_candidate_20261113_r01').iterdir()if p.is_file()]+
        [str(p.relative_to(ROOT))for p in(ROOT/'verification/run18/diagnostics_20261113').iterdir()if p.is_file()]+
        [str(p.relative_to(ROOT))for p in(ROOT/'verification/run18/runs/release_candidate_20261113_r02').iterdir()if p.is_file()]+
        [str(p.relative_to(ROOT))for p in(ROOT/'verification/run18/continuation_20261114').iterdir()if p.is_file()]+
        [str(p.relative_to(ROOT))for p in(ROOT/'verification/run18/antipodal_20261114').iterdir()if p.is_file()])
    initial={f:sha(ROOT/f)for f in bound}
    source_snapshot=git('rev-parse','HEAD').decode().strip()
    (out/'SOURCE_SHA256.json').write_text(json.dumps(initial,indent=2)+'\n')
    dependency=dict(lean_version=subprocess.check_output(['lean','--version'],text=True).strip(),
        mathlib_commit=subprocess.check_output(['git','-C',str(ROOT/'.lake/packages/mathlib'),'rev-parse','HEAD'],text=True).strip(),
        source_snapshot_commit=source_snapshot,fixture_threads=1,fixture_memory_limit_mib=12288)
    assert 'version 4.36.0-rc2,'in dependency['lean_version']
    assert dependency['mathlib_commit']=='139105d28c7685a154cb3093f79edb2e16708099'
    (out/'snapshot.json').write_text(json.dumps(dependency,indent=2)+'\n')
    assert sha(ROOT/'audit/run18/RequestedGoals.lean')==FROZEN
    for f in valid_new+['NSP14.lean']:
        assert not re.search(r'\b(?:sorry|admit|sorryAx|native_decide)\b|^\s*(?:private\s+|public\s+)?axiom\b',(ROOT/f).read_text(),re.M),f
    records=[]
    def run(name,command,expected=None,compressed=False):
        start=time.monotonic();r=subprocess.run(command,cwd=ROOT,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
        data=r.stdout.encode();(out/(name+('.log.gz'if compressed else'.log'))).write_bytes(gzip.compress(data,mtime=0)if compressed else data)
        ok=(r.returncode==0 and not re.search(r'\bwarning:',r.stdout))if expected is None else(r.returncode==1 and expected in r.stdout and 'lean.unknownIdentifier'in r.stdout and 'does not exist'not in r.stdout)
        records.append(dict(name=name,command=command,exit_code=r.returncode,expected_missing_declaration=expected,passed=ok,seconds=round(time.monotonic()-start,3)))
        print(name,r.returncode,'EXPECTED_OPEN'if expected else'PASS'if ok else'FAIL',flush=True)
        if not ok:
            (out/'failure.json').write_text(json.dumps(dict(status='FAILED_VALIDATION_ATTEMPT',run18_complete=False,
                source_snapshot_commit=source_snapshot,checks=records,failed_check=name),indent=2)+'\n')
            print(r.stdout[:12000]);raise SystemExit(1)
        return r.stdout
    if args.fresh_test_cache:
        backup=Path(tempfile.mkdtemp(prefix='nsp14-run18-cache-'));moved=[]
        for f in ['.lake/build/lib/lean/tests','.lake/build/lib/lean/NSP14/Lex','.lake/build/lib/lean/NSP14/Width',
                  '.lake/build/ir/NSP14/Lex','.lake/build/ir/NSP14/Width','.lake/build/lib/lean/audit/run18']:
            p=ROOT/f
            if p.exists():shutil.move(str(p),str(backup/f.replace('/','_')));moved.append(f)
        for d in ['.lake/build/lib/lean','.lake/build/ir']:
            for p in(ROOT/d).glob('NSP14.*'):
                if p.is_file():shutil.move(str(p),str(backup/(d.replace('/','_')+'_'+p.name)))
        (out/'fresh_cache.json').write_text(json.dumps(dict(backup=str(backup),moved=moved),indent=2)+'\n')
    run('build',['lake','build','NSP14','Mathlib.Algebra.Field.ZMod'])
    prior=json.loads((ROOT/'verification/run17/runs/release_candidate_20261113_r02/verification.json').read_text())
    paths=list(prior['fixture_order'])+sorted(f for f in valid_new if f.startswith('tests/')or f.startswith('audit/'))
    ordered=[];active=set()
    def emit(f):
        if f in ordered:return
        assert f not in active,('fixture cycle',f)
        active.add(f)
        for m in re.findall(r'^\s*(?:public\s+)?import\s+((?:tests|audit)\.[\w.]+)',(ROOT/f).read_text(),re.M):emit(m.replace('.','/')+'.lean')
        active.remove(f);ordered.append(f)
    for f in paths:emit(f)
    for i,f in enumerate(ordered):
        target=Path('.lake/build/lib/lean')/Path(f).with_suffix('.olean');(ROOT/target).parent.mkdir(parents=True,exist_ok=True)
        run('fixture_'+str(i).zfill(3)+'_'+Path(f).stem,['lake','env','lean','-j1','-M12288',f,'-o',str(target)])
    for f in open_acceptances:
        text=(ROOT/f).read_text();required=re.findall(r':=\s*([\w.]+)\s*$',text,re.M)
        assert len(required)==1,(f,required)
        run('open_'+Path(f).stem,['lake','env','lean','-j1','-M12288',f],expected=required[0])
    run('width_model',['python3','scripts/check_run18_width.py','--output',str(rel/'width_checks.json')])
    run('continuation_model',['python3','scripts/check_run18_continuation.py','--output',str(rel/'continuation_checks.json')])
    run('five_model',['python3','scripts/check_run18_five.py','--output',str(rel/'five_checks.json')])
    run('publication_guards',['python3','scripts/check_run18_guards.py'])
    run('axiom_policy_controls',['python3','scripts/check_run18_axiom_policy.py','--output-dir',str(rel/'axiom_policy_controls')])
    for mode in ['schedule','coordinates']:
        run('inherited_'+mode,['python3','scripts/replay_run17_inherited.py',mode,'--output',str(rel/('inherited_'+mode+'.json'))])
    run('inherited_additive',['python3','scripts/check_run17_additive.py','--output',str(rel/'inherited_additive.json')])
    modules=[f[:-5].replace('/','.')for f in ordered]
    newmodules=[f[:-5].replace('/','.')for f in valid_new]+['NSP14']
    audit='''module
import NSP14
'''+''.join('import '+m+'\n'for m in modules)+'''import Lean
open Lean
set_option maxRecDepth 4000
set_option maxHeartbeats 0
#eval show MetaM Unit from do
 let env ← getEnv
 let included : Array String := #['''+','.join(json.dumps(m)for m in modules)+''']
 let newModules : Array String := #['''+','.join(json.dumps(m)for m in newmodules)+''']
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
   let mut fields := [("name",toJson n.toString),("module",toJson modName),("kind",toJson kind),("axioms",toJson (axs.map Name.toString))]
   if newModules.contains modName then
    let type ← Lean.Meta.ppExpr ci.type
    let explicitType ← withOptions (fun opts => opts.setBool `pp.explicit true) (Lean.Meta.ppExpr ci.type)
    fields := fields ++ [("type",toJson type.pretty),("explicit_type",toJson explicitType.pretty)]
   IO.println ((Json.mkObj fields).compress)
'''
    (out/'EnvironmentAudit.lean').write_text(audit)
    raw=run('environment_axioms',['lake','env','lean','-j1','-M12288',str(rel/'EnvironmentAudit.lean')],compressed=True)
    declarations=[json.loads(l)for l in raw.splitlines()if l.startswith('{')]
    assert declarations and len({d['name']for d in declarations})==len(declarations)
    for d in declarations:
        assert set(d['axioms'])<=ALLOWED and d['name']not in d['axioms'],d
        d['exported_kind']=d['kind'];d['kind']=validated_kind(d)
        d['source']=d['module'].replace('.','/')+'.lean';d['source_sha256']=sha(ROOT/d['source'])
    newdecls=[d for d in declarations if d['source']in valid_new]
    assert set(valid_new)<={d['source']for d in newdecls}
    assert all('type'in d and'explicit_type'in d for d in newdecls)
    names={d['name']for d in declarations}
    assert {'NSP14.Run18.five_closed','NSP14.NumericalSemigroup.narrow_five_comparison','NSP14.Run18.sparse_closed','NSP14.NumericalSemigroup.narrow_sparse_comparison','Run15Closed.all_original_goals_closed','NSP14.Run17.kneser_closed','NSP14.Run17.savchevChen_closed'}<=names
    assert not {'NSP14.Lex.bhp_ek','NSP14.Run18.edge_closed','NSP14.Run18.dense_closed','NSP14.Run18.width_closed'}&names
    assert git('rev-parse','HEAD').decode().strip()==source_snapshot,'HEAD changed during verification'
    assert {f:sha(ROOT/f)for f in bound}==initial,'source changed during verification'
    assert {f:sha(ROOT/f)for f in retained}==retained,'inherited evidence changed'
    for f in old-append_only:assert(ROOT/f).read_bytes()==git('show',BASE+':'+f),f
    (out/'declarations.json.gz').write_bytes(gzip.compress((json.dumps(sorted(declarations,key=lambda d:d['name']),ensure_ascii=False,indent=2)+'\n').encode(),mtime=0))
    (out/'SOURCE_SHA256.json').write_text(json.dumps(initial,indent=2)+'\n')
    summary=dict(status='PASS_RUN18_PARTIAL_VALIDATION',run18_complete=False,baseline_commit=BASE,
        proof_snapshot_commit=source_snapshot,fixture_threads=1,fixture_memory_limit_mib=12288,fresh_project_test_cache=args.fresh_test_cache,
        fresh_new_production_cache=args.fresh_test_cache,evidence_directory=str(rel),checks=records,
        fixture_order=ordered,expected_open_acceptances=open_acceptances,allowed_axioms=sorted(ALLOWED),
        environment_declarations=len(declarations),new_environment_declarations=len(newdecls),
        sources=valid_new,preserved_evidence_count=len(retained),closed_ids=['W_SPARSE','W_FIVE'],
        unproved_ids=['X_BHP_EK','W_EDGE','W_DENSE','W_CLOSE'],frozen_requested_goals_sha256=FROZEN)
    (out/'verification.json').write_text(json.dumps(summary,ensure_ascii=False,indent=2)+'\n')
    manifest={str(p.relative_to(ROOT)):sha(p)for p in sorted(out.rglob('*'))if p.is_file()and p.name!='MANIFEST_SHA256.json'}
    (out/'MANIFEST_SHA256.json').write_text(json.dumps(manifest,indent=2)+'\n')
    print(summary['status'],len(records),'commands',len(declarations),'declarations',len(newdecls),'new',flush=True)
if __name__=='__main__':main()
