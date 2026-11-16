#!/usr/bin/env python3
"""Source-bound Run19 certification. Retains all 289 V06 check identities.

Fresh means the entire project lib/IR/test/audit cache, not mathlib's fixed cache.
The immutable V06 verifier is imported only for its audit/serialization helpers.
"""
from pathlib import Path
import argparse, datetime, gzip, hashlib, importlib.util, json, os, re, shutil, subprocess, tempfile, time

ROOT=Path(__file__).resolve().parents[1]
BASE='04906ede0e9e3a04b9c07c791c1e1c49834dd3e1'
PRIOR='verification/run18/runs/v06_alignment_20261115T152000Z_r01'
POLICY='docs/RUN19_CHANGE_POLICY.json'
FROZEN='verification/run19/sources/initial_contracts_20261116/FROZEN_SHA256.json'
FULL_IDS={'N_DISTANCE','N_WORDS','N_HIGH','N_FIRST','N_SMALL','N_WIDTH4','N_CLOSE','I_BASE','X_LTV','I_THREE'}
# Independent source-declaration inventory, confirmed by the whole-branch reviewer.
# A generated equation row alone must not satisfy an entire fixture's coverage.
FIXTURE_HELPERS={
 'tests.N4StandardWords':('NSP14.Tests.Run19Words',['collective','ca','cb','collective_pair','neither_unit','collective_triangle','mixed_both_orders','small_height_and_socle']),
 'tests.N4Higher':('NSP14.Tests.Run19Higher',['heTwo','all_fields']),
 'tests.N4Small':('NSP14.Tests.Run19Small',['six','seven','eight']),
 'tests.N4WidthFour':('NSP14.Tests.Run19WidthFour',['data']),
 'tests.N4ActualClosure':('NSP14.Tests.Run19N4NonCM',['D','cap']),
 'tests.SmallEmbeddingBase':('NSP14.Tests.Run19Base',['naturals','naturals_atoms','naturals_embedding','naturals_width_zero','twoThree','threeFive']),
 'tests.LTVActual':('NSP14.Tests.Run19Three',['narrowNonCM','cm','boundaryWide','nonCM_embedding']),
 'tests.SmallEmbeddingThree':('NSP14.Tests.Run19ThreeFullAP',['unitStep','nonunitStep']),
}
spec=importlib.util.spec_from_file_location('v06_helpers',ROOT/'scripts/verify_v06_alignment.py')
v06=importlib.util.module_from_spec(spec);spec.loader.exec_module(v06)
sha=v06.sha;git=v06.git;safe=v06.safe;write_json=v06.write_json
evidence_manifest=v06.evidence_manifest;check_evidence_manifest=v06.check_evidence_manifest
validate_audit=v06.validate_audit;validate_import_coverage=v06.validate_import_coverage

def source_manifest(root):
    # These are executable checker code and frozen input receipts, despite their
    # provenance-directory location. Bind them to Git exactly like scripts/.
    result=v06.source_manifest(root)
    for path in (root/'verification/run19/sources').rglob('*'):
        if path.is_file() and '__pycache__' not in path.parts and path.suffix!='.pyc':
            result[str(path.relative_to(root))]=sha(path.read_bytes())
    return dict(sorted(result.items()))

def check_source_manifest(root,manifest,proof_commit=None):
    if source_manifest(root)!=manifest:raise ValueError('source manifest content or fileset changed')
    if proof_commit:
        for name,digest in manifest.items():
            if sha(git(root,'show',proof_commit+':'+name))!=digest:
                raise ValueError('source is not committed in proof snapshot: '+name)

def validate_output(root,name):
    path=safe(root,name);p=Path(name)
    if len(p.parts)!=4 or p.parts[:3]!=('verification','run19','runs') or not re.fullmatch(r'[A-Za-z0-9_-]+',p.name):
        raise ValueError('unique verification/run19/runs/<id> required')
    if path.exists():raise ValueError('output already exists')
    return path

def policy_files(root):
    policy=json.loads((root/POLICY).read_text())
    if policy['base']!=BASE or policy['modified_files']!=[]:raise ValueError('fixed policy differs')
    groups=['new_production','new_fixtures','new_audits','new_infrastructure']
    return policy,set().union(*(set(policy[g]) for g in groups))

def validate_changes(root,require_new=True):
    policy,allowed=policy_files(root)
    # Bind the allowlist to the preimplementation commit, not a mutable JSON.
    frozen_policy=git(root,'show','e13d8d1:'+POLICY)
    if (root/POLICY).read_bytes()!=frozen_policy:raise ValueError('fixed policy bytes changed')
    old={l.split('\t',1)[1]:l.split()[2] for l in git(root,'ls-tree','-r',BASE).decode().splitlines()}
    actual=v06.current_files(root)
    if not set(old)<=actual:raise ValueError('inherited files missing')
    for name,oid in old.items():
        data=safe(root,name).read_bytes()
        if name in policy['append_only']:
            if not data.startswith(git(root,'show',BASE+':'+name)):raise ValueError('append-only prefix changed: '+name)
        elif v06.blob_oid(data)!=oid:raise ValueError('forbidden inherited edit: '+name)
    extra=actual-set(old)-allowed
    extra={p for p in extra if not p.startswith('verification/run19/') and not
           (p.startswith('artifacts/NS_P14_LEAN_RUN19_') and p.endswith('.zip'))}
    # Concurrent upstream plan-only additions are admitted only by their exact Git bytes.
    inherited_docs=set()
    upstream='a16bb2b'
    for line in git(root,'diff','--name-status',BASE,upstream).decode().splitlines():
        kind,name=line.split('\t')
        if kind!='A' or not name.startswith('docs/superpowers/'):
            raise ValueError('unexpected upstream integration scope')
        if name in extra and safe(root,name).read_bytes()==git(root,'show',upstream+':'+name):inherited_docs.add(name)
    extra-=inherited_docs
    if extra:raise ValueError('files outside finite allowlist: '+repr(sorted(extra)))
    if require_new and not allowed<=actual:raise ValueError('required files missing: '+repr(sorted(allowed-actual)))
    if (root/FROZEN).read_bytes()!=git(root,'show','e13d8d1:'+FROZEN):raise ValueError('frozen hash receipt changed')
    frozen=json.loads((root/FROZEN).read_text())
    for name,digest in frozen.items():
        if sha(safe(root,name).read_bytes())!=digest:raise ValueError('frozen contract changed: '+name)
    for name in set(policy['new_production'])|set(policy['new_fixtures'])|set(policy['new_audits']):
        if (root/name).exists() and v06.TOKEN.search((root/name).read_text()):raise ValueError('forbidden proof token: '+name)
    return policy

def validate_coverage(prior,records,fixtures):
    if len(prior['checks'])!=289 or len(prior['fixture_order'])!=273:raise ValueError('fixed V06 inventory differs')
    if {r['name'] for r in prior['checks']}-{r['name'] for r in records}:raise ValueError('inherited check coverage missing')
    if set(prior['fixture_order'])-set(fixtures):raise ValueError('inherited fixture coverage missing')
    if not {'v06_routes','v06_alignment_controls','environment_axioms','base_build','base_environment_types'} <= {r['name'] for r in records}:
        raise ValueError('V06 route/type coverage missing')

def validate_named_helpers(rows):
    actual={(r['module'],r['name']) for r in rows if 'type' in r and 'explicit_type' in r and 'axioms' in r}
    required={(m,prefix+'.'+name) for m,(prefix,names) in FIXTURE_HELPERS.items() for name in names}
    if required-actual:raise ValueError('named fixture helper coverage missing: '+repr(sorted(required-actual)))

def audit_source(imports,typed_modules):
    # Lean's module system hides private/generated declarations from ordinary
    # imports. Import each audited module's full view explicitly; genuine empty
    # import-only modules keep their ordinary import/metadata coverage.
    text=v06.audit_source(set(imports)|set(typed_modules),typed_modules)
    for module in typed_modules:
        text=text.replace('import '+module+'\n','import all '+module+'\n')
    return text

def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--output-dir');p.add_argument('--fresh-test-cache',action='store_true')
    p.add_argument('--preflight',action='store_true');p.add_argument('--baseline-cache');a=p.parse_args();created=False
    try:
        policy=validate_changes(ROOT,require_new=not a.preflight)
        if a.preflight:print('PASS_RUN19_PREFLIGHT_NOT_CERTIFICATION');return
        if not a.fresh_test_cache:raise ValueError('--fresh-test-cache required')
        rel=a.output_dir or 'verification/run19/runs/release_'+datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%SZ')
        out=validate_output(ROOT,rel)
        proof=git(ROOT,'rev-parse','HEAD').decode().strip()
        initial=source_manifest(ROOT);check_source_manifest(ROOT,initial,proof)
        prior=json.loads((ROOT/PRIOR/'verification.json').read_text())
        if len(prior['checks'])!=289 or len(prior['fixture_order'])!=273:raise ValueError('fixed V06 inventory differs')
        retained=v06.preserve_evidence(ROOT,out)
        out.mkdir(parents=True,exist_ok=False);created=True;records=[]
        write_json(out/'SOURCE_SHA256.json',initial);write_json(out/'INHERITED_EVIDENCE_SHA256.json',retained)
        snapshot={'proof_snapshot_commit':proof,'base':BASE,'lean':subprocess.check_output(['lean','--version'],text=True).strip(),
          'mathlib':git(ROOT/'.lake/packages/mathlib','rev-parse','HEAD').decode().strip()}
        if 'version 4.36.0-rc2,' not in snapshot['lean'] or snapshot['mathlib']!=v06.MATHLIB:raise ValueError('pin mismatch')
        write_json(out/'snapshot.json',snapshot)
        def invariant():
            if git(ROOT,'rev-parse','HEAD').decode().strip()!=proof:raise ValueError('HEAD changed')
            check_source_manifest(ROOT,initial)
        def run(name,command,cwd=ROOT,compressed=False,expected=None):
            invariant();start=time.monotonic()
            result=subprocess.run(command,cwd=cwd,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
            data=result.stdout.encode();(out/(name+('.log.gz' if compressed else '.log'))).write_bytes(gzip.compress(data,mtime=0) if compressed else data)
            ok=result.returncode==0 and not re.search(r'\bwarning:',result.stdout)
            if expected is not None:ok=result.returncode==1 and expected in result.stdout and 'lean.unknownIdentifier' in result.stdout and 'does not exist' not in result.stdout
            records.append({'name':name,'command':command,'cwd':str(cwd),'exit_code':result.returncode,'passed':ok,'seconds':round(time.monotonic()-start,3)})
            write_json(out/'checks.in_progress.json',records);print(name,result.returncode,'PASS' if ok else 'FAIL',flush=True)
            invariant()
            if not ok:raise ValueError('check failed: '+name)
            return result.stdout
        backup=Path(tempfile.mkdtemp(prefix='run19-cold-cache-'));moved=[]
        for name in ['.lake/build/lib/lean','.lake/build/ir']:
            source=ROOT/name
            if source.exists():
                dest=backup/name.replace('/','_');shutil.move(str(source),str(dest));moved.append({'from':name,'to':str(dest)})
        write_json(out/'fresh_cache.json',{'whole_project_lib_ir_tests_audits':True,'moved':moved,'fixed_mathlib_cache_retained':True})
        fixtures=v06.fixture_order(ROOT,prior['fixture_order']+sorted(set(policy['new_fixtures'])|set(policy['new_audits'])))
        typed=set(v06.AUDITED_MODULES)|{n[:-5].replace('/','.') for n in policy['new_production']+policy['new_fixtures']+policy['new_audits']}
        # Empty import-only modules are checked through actual environment module metadata.
        import_only={m for m in typed if not re.search(r'^(?:private |noncomputable )*(?:def|theorem|lemma|instance|structure|inductive|abbrev)\b',
            (ROOT/(m.replace('.','/')+'.lean')).read_text(),re.M)}
        typed-=import_only
        (out/'EnvironmentAudit.lean').write_text(audit_source(['NSP14']+[n[:-5].replace('/','.') for n in fixtures],typed))
        mapping=[];raw_environment=None
        for old in prior['checks']:
            name=old['name']
            if name.startswith(('fixture_','v06_fixture_')):continue
            if name=='build':
                command=['lake','build','NSP14','Mathlib.Algebra.Field.ZMod'];run(name,command)
                for index,f in enumerate(fixtures):
                    dest=Path('.lake/build/lib/lean')/Path(f).with_suffix('.olean');(ROOT/dest).parent.mkdir(parents=True,exist_ok=True)
                    oldrow=next((r for r in prior['checks'] if r['name'].startswith(('fixture_','v06_fixture_')) and f in r['command']),None)
                    label=oldrow['name'] if oldrow else 'run19_fixture_'+str(index).zfill(3)+'_'+Path(f).stem
                    cmd=['lake','env','lean','-j1','-M12288',f,'-o',str(dest)]
                    run(label,cmd,expected=oldrow.get('expected_missing_declaration') if oldrow else None)
                    mapping.append({'name':label,'old_command':oldrow['command'] if oldrow else None,'new_command':cmd})
            elif name=='environment_axioms':
                cmd=['lake','env','lean','-j1','-M12288',str(out.relative_to(ROOT)/'EnvironmentAudit.lean')]
                raw_environment=run(name,cmd,compressed=True)
            elif name in {'base_build','base_environment_types'}:continue
            else:
                cmd=['python3','scripts/replay_run19_inherited.py','--name',name,'--output-dir',str(Path(rel)/('replay_'+name))]
                run(name,cmd)
            mapping.append({'name':name,'old_command':old['command'],'new_command':command if name=='build' else cmd})
        # The old base/type checks have a different source by definition; identity is checked before copying its cache.
        base_rows=v06.baseline_audit(ROOT,out,run,a.baseline_cache)
        mapping.extend({'name':n,'old_command':next(r['command'] for r in prior['checks'] if r['name']==n),
                        'new_command':next(r['command'] for r in records if r['name']==n)} for n in ['base_build','base_environment_types'])
        write_json(out/'COMMAND_MAP.json',mapping)
        rows,metadata=v06.parse_audit(raw_environment)
        validate_import_coverage(metadata,typed|import_only|{'NSP14'})
        validate_audit(rows,typed,base_rows)
        # Also compare every V06 typed public declaration against its successfully certified version.
        old_rows=json.loads(gzip.decompress((ROOT/PRIOR/'declarations.json.gz').read_bytes()))
        old_typed=[r for r in old_rows if 'explicit_type' in r]
        validate_audit(rows,typed,old_typed)
        validate_named_helpers(rows)
        write_json(out/'environment_import_coverage.json',metadata)
        for r in rows:
            r['source_sha256']=initial[r['module'].replace('.','/')+'.lean']
        (out/'declarations.json.gz').write_bytes(gzip.compress(json.dumps(rows,ensure_ascii=False).encode(),mtime=0))
        write_json(out/'audit_coverage.json',{'typed_modules':sorted(typed),'import_only_modules':sorted(import_only),
            'declarations':len(rows),'typed_declarations':sum('type'in r for r in rows),'base_public_types_preserved':True,
            'v06_public_types_preserved':True,'allowed_axioms':sorted(v06.ALLOWED_AXIOMS),
            'direct_import_all_for_each_typed_module':True,'private_and_generated_support_included':True})
        write_json(out/'named_helper_coverage.json',{'required':{m:[prefix+'.'+n for n in names]
          for m,(prefix,names) in FIXTURE_HELPERS.items()},'count':sum(len(names) for _,names in FIXTURE_HELPERS.values()),
          'all_present_with_normal_explicit_types_and_axioms':True,
          'generated_support_declarations_also_enumerated_by_environment_audit':True})
        run('run19_routes',['python3','scripts/check_run19_routes.py','--output',str(Path(rel)/'routes.json')])
        run('run19_exact_models',['python3','scripts/check_run19_n4.py','--output',str(Path(rel)/'models.json')])
        run('run19_negative_controls',['python3','scripts/check_run19_guards.py','--output',str(Path(rel)/'guards.json')])
        validate_coverage(prior,records,fixtures);invariant();validate_changes(ROOT)
        if v06.preserve_evidence(ROOT,out)!=retained:raise ValueError('inherited evidence bytes/fileset changed')
        summary={'status':'PASS_RUN19_COMPLETE_VALIDATION','mathematical_contracts_closed':True,'run19_complete':False,
          'completion_pending':['fresh_independent_review','audit_package','normal_push'],
          'closed_ids':sorted(FULL_IDS),'unproved_ids':[],'proof_snapshot_commit':proof,'base':BASE,
          'evidence_directory':rel,'checks':records,'fixture_order':fixtures,'inherited_check_count':289,
          'inherited_fixture_count':273,'fresh_whole_project_cache':True,'fixed_mathlib_cache_retained':True,
          'normal_explicit_type_and_axiom_coverage':sorted(typed),'verified_import_only_modules':sorted(import_only),
          'environment_declarations':len(rows),'preserved_evidence_count':len(retained),'allowed_axioms':sorted(v06.ALLOWED_AXIOMS),
          'not_claimed':['all_P14','stronger_LTV_linear_bounds','generic_initial_ideal_equality']}
        write_json(out/'verification.json',summary);write_json(out/'MANIFEST_SHA256.json',evidence_manifest(ROOT,out))
        print(summary['status'],len(records),'checks',len(fixtures),'fixtures',len(rows),'declarations',flush=True)
    except (ValueError,OSError,subprocess.CalledProcessError,KeyError) as exc:
        if created:write_json(out/'failure.json',{'status':'FAILED_RUN19_ATTEMPT','error':str(exc),'checks':locals().get('records',[])})
        p.exit(1,str(exc)+'\n')

if __name__=='__main__':main()
