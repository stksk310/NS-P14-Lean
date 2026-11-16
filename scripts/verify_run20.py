#!/usr/bin/env python3
"""Final P14 certification: all project modules, private declarations, all rows.

Only project cache is cold. Fixed mathlib package cache is retained explicitly.
"""
from pathlib import Path
import argparse, datetime, gzip, importlib.util, json, os, re, shutil, subprocess, tempfile, time
ROOT=Path(__file__).resolve().parents[1]
BASE='07fe1ed952ae31ce01255ce53df538bf0a76d5cc'
UPSTREAM_AUDIT='342fbdda072fc5d6aa5e8f2d8968456cc54c12a6'
RUN19_PROOF='7c6821ee0f43869b2a9b5d9b1b72b8d7a045b4a7'
PRIOR='verification/run19/runs/release_20261116_r03'
POLICY='docs/RUN20_CHANGE_POLICY.json'
FROZEN='verification/run20/sources/initial_contracts_20261116/FROZEN_SHA256.json'
FULL_IDS={'I_PARTITION','I_MAIN'}
def load(name,path):
    spec=importlib.util.spec_from_file_location(name,path);m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m);return m
old=load('run20_helpers',ROOT/'scripts/verify_run19.py');v06=old.v06
sha=old.sha;git=old.git;safe=old.safe;write_json=old.write_json
evidence_manifest=old.evidence_manifest;check_evidence_manifest=old.check_evidence_manifest

def preserve_evidence(root,excluded):
    # Imports may create interpreter caches in a clean reproduction. They are
    # not historical evidence. Every tracked path remains bound, even a .pyc.
    tracked=set(git(root,'ls-files','-z','--cached').decode().split('\0'))
    return {n:h for n,h in v06.preserve_evidence(root,excluded).items()
      if n in tracked or not ('__pycache__' in Path(n).parts and n.endswith('.pyc'))}

def source_manifest(root):
    result=v06.source_manifest(root)
    for folder in ['verification/run19/sources','verification/run20/sources']:
        for p in (root/folder).rglob('*'):
            if p.is_file() and '__pycache__' not in p.parts and p.suffix!='.pyc':result[str(p.relative_to(root))]=sha(p.read_bytes())
    return dict(sorted(result.items()))

def check_source_manifest(root,manifest,proof_commit=None):
    if source_manifest(root)!=manifest:raise ValueError('source manifest content or fileset changed')
    if proof_commit:
        for name,digest in manifest.items():
            if sha(git(root,'show',proof_commit+':'+name))!=digest:raise ValueError('source not committed in proof snapshot: '+name)

def validate_output(root,name):
    path=safe(root,name);p=Path(name)
    if len(p.parts)!=4 or p.parts[:3]!=('verification','run20','runs') or not re.fullmatch(r'[A-Za-z0-9_-]+',p.name):raise ValueError('unique verification/run20/runs/<id> required')
    if path.exists():raise ValueError('output already exists')
    return path

def validate_changes(root,require_new=True):
    policy=json.loads((root/POLICY).read_text())
    if (root/POLICY).read_bytes()!=git(root,'show','bcadd3b:'+POLICY):raise ValueError('fixed change policy differs')
    if policy['base']!=BASE or policy['modified_files']:raise ValueError('fixed policy base differs')
    allowed=set().union(*(set(policy[g]) for g in ['new_production','new_fixtures','new_audits','new_infrastructure']))
    inherited={l.split('\t',1)[1]:l.split()[2] for l in git(root,'ls-tree','-r',BASE).decode().splitlines()}
    # Arrived independent Run19 audit: exact immutable upstream bytes only.
    # This supplements, and does not rewrite, the preimplementation policy.
    adopted=set(git(root,'diff','--name-only',BASE,UPSTREAM_AUDIT).decode().splitlines())
    for name in adopted:
        if safe(root,name).read_bytes()!=git(root,'show',UPSTREAM_AUDIT+':'+name):raise ValueError('arrived audit Git bytes differ: '+name)
    actual=v06.current_files(root)
    if not set(inherited)<=actual:raise ValueError('inherited files missing')
    for name,oid in inherited.items():
        data=safe(root,name).read_bytes()
        if name in policy['append_only']:
            if not data.startswith(git(root,'show',BASE+':'+name)):raise ValueError('append-only prefix changed: '+name)
        elif name not in adopted and v06.blob_oid(data)!=oid:raise ValueError('forbidden inherited edit: '+name)
    extra={p for p in actual-set(inherited)-allowed-adopted if not p.startswith('verification/run20/') and not
      (p.startswith('artifacts/NS_P14_LEAN_RUN20_') and p.endswith('.zip'))}
    if extra:raise ValueError('files outside finite allowlist: '+repr(sorted(extra)))
    if require_new and not allowed<=actual:raise ValueError('required files missing: '+repr(sorted(allowed-actual)))
    if (root/FROZEN).read_bytes()!=git(root,'show','996d982:'+FROZEN):raise ValueError('frozen receipt changed')
    for name,digest in json.loads((root/FROZEN).read_text()).items():
        if sha(safe(root,name).read_bytes())!=digest:raise ValueError('frozen contract changed: '+name)
    # Requested.I_PARTITION refers to these five predicates by name. Freeze
    # their original definitions and context, not merely the wrapper's type.
    # The only pre-proof addition is this explicitly enumerated needed import.
    partition='NSP14/Main/Partition.lean'
    initial_partition=git(root,'show','996d982:'+partition)
    initial_partition=initial_partition.replace(b'public import NSP14.Semigroup.WidthNormalization\n',
      b'public import NSP14.Semigroup.WidthNormalization\npublic import NSP14.Endpoint.OffsetOrder\n',1)
    if not safe(root,partition).read_bytes().startswith(initial_partition):raise ValueError('frozen partition predicate bodies changed')
    for name in policy['new_production']+policy['new_fixtures']+policy['new_audits']:
        if (root/name).exists() and v06.TOKEN.search((root/name).read_text()):raise ValueError('forbidden proof token: '+name)
    return policy

def project_modules(root):
    files={'NSP14.lean'}|{str(p.relative_to(root)) for folder in ['NSP14','tests','audit'] for p in (root/folder).rglob('*.lean')}
    return {n[:-5].replace('/','.') for n in files}

def dependency_snapshot(root):
    result={}
    for item in json.loads((root/'lake-manifest.json').read_text())['packages']:
        package=root/'.lake/packages'/item['name'];head=git(package,'rev-parse','HEAD').decode().strip()
        dirty=git(package,'status','--porcelain','--untracked-files=no').decode().strip()
        extra=[n for n in git(package,'ls-files','--others','--exclude-standard').decode().splitlines() if n.endswith('.lean')]
        if head!=item['rev'] or dirty or extra:raise ValueError('fixed dependency source mismatch: '+item['name'])
        result[item['name']]={'commit':head,'tracked_clean':True,'untracked_Lean_sources':[]}
    return result

def audit_source(modules,selected=None,row_output=None):
    text=old.audit_source(modules,modules)
    selected=set(modules) if selected is None else set(selected)
    if not selected<=set(modules):raise ValueError('audited modules outside full imports')
    text=re.sub(r' let typed : Array String := #[^\n]*',
      ' let typed : Array String := #["'+'","'.join(sorted(selected))+'"]\n let typedSet := Std.HashSet.ofArray typed',text,count=1)
    text=text.replace('typed.contains modName','typedSet.contains modName')
    # Full kernel rendering retains every argument and universe without the
    # pretty-printer's deep-term/proof elisions. Alpha-normalize binder names
    # for reproducible base comparison; all binder kinds and constants remain.
    canonical=(ROOT/'verification/run20/sources/kernel_type_codec.inc').read_text()
    text=text.replace('open Lean\n','open Lean\n'+canonical,1)
    text=text.replace('let explicitType ← withOptions (fun opts => opts.setBool `pp.explicit true) (Lean.Meta.ppExpr ci.type)',
      'let canonicalType := Run20TypeEncoding.canonical 0 ci.type\n    unless canonicalType == ci.type do throwError "kernel type alpha roundtrip failed: {n}"\n    if ci.type.getUsedConstants.any (fun c => c.toString.startsWith "__run20_binder_") then throwError "kernel binder namespace collision: {n}"\n    let explicitType := toString canonicalType')
    text=text.replace('let type ← Lean.Meta.ppExpr ci.type','let type ← Lean.Meta.withFreshCache (Lean.Meta.ppExpr ci.type)')
    text=text.replace('let explicitType := toString canonicalType', 'let (explicitDag,explicitMetadata) ← ofExcept (Run20TypeEncoding.pack canonicalType)\n    let (originalDag,originalMetadata) ← ofExcept (Run20TypeEncoding.pack ci.type)\n    let explicitType := explicitDag.compress')
    text=text.replace('toJson explicitType.pretty','toJson explicitType')
    text=text.replace('("explicit_type",toJson explicitType)]',
      '("explicit_type",toJson explicitType),("kernel_type",toJson originalDag.compress),("kernel_metadata",originalMetadata),("explicit_metadata",explicitMetadata),("kernel_dag_roundtrip",toJson true),("kernel_alpha_roundtrip",toJson true),("universe_parameters",toJson (ci.levelParams.map Name.toString))]')
    text=text.replace('   IO.println ((Json.mkObj fields).compress)',
      '''   if #["NSP14.NumericalSemigroup.p14_totalBetti_le_intervalCompletion","NSP14.Run20.partition_closed","NSP14.Run20.main_closed"].contains n.toString then
    let pretty ← withOptions (fun o => o.setBool `pp.all true |>.setBool `pp.tagAppFns false) (Lean.Meta.ppExpr ci.type)
    fields := fields ++ [("pretty_explicit_type",toJson pretty.pretty)]
   IO.println ((Json.mkObj fields).compress)''',1)
    text=text.replace('modName == "NSP14" || modName.startsWith "NSP14." || modName == "tests" || modName.startsWith "tests." || modName.startsWith "audit."','typedSet.contains modName')
    # An independently emitted environment inventory detects a dropped row even
    # when its module still has thousands of other declarations.
    marker=' for (n,ci) in env.constants.toList do'
    inventory=''' let mut inventory : Array String := #[]
 for (n,_) in env.constants.toList do
  let some idx := env.getModuleIdxFor? n | continue
  let modName := env.header.moduleNames[idx.toNat]!.toString
  if typedSet.contains modName then inventory := inventory.push n.toString
 IO.println ((Json.mkObj [("declaration_inventory",toJson inventory)]).compress)
'''
    text=text.replace(marker,inventory+marker,1)
    if row_output is not None:
        text=text.replace('   IO.println ((Json.mkObj fields).compress)',
          '   IO.FS.withFile '+json.dumps(str(row_output))+' .append fun h => h.putStrLn ((Json.mkObj fields).compress)',1)
    return text

def parse_audit(raw):
    lines=raw.splitlines();inventories=[json.loads(s) for s in lines if s.startswith('{') and '"declaration_inventory"' in s]
    if len(inventories)!=1:raise ValueError('declaration inventory missing')
    raw='\n'.join(s for s in lines if not (s.startswith('{') and '"declaration_inventory"' in s))
    rows,meta=v06.parse_audit(raw);meta['declaration_inventory']=inventories[0]['declaration_inventory'];return rows,meta

def validate_full_audit(rows,meta,modules,base_rows=None,expected_names=None):
    v06.validate_import_coverage(meta,modules)
    v06.validate_audit(rows,{r['module'] for r in rows},base_rows,set(meta['declaration_inventory']))
    if expected_names is not None and (set(meta['declaration_inventory'])!=set(expected_names) or {r['name'] for r in rows}!=set(expected_names)):
        raise ValueError('independent frozen declaration-name coverage differs')
    if base_rows is not None and {r['name'] for r in base_rows}-{r['name'] for r in rows}:
        raise ValueError('inherited private/public declaration-name coverage missing')
    if {r['module'] for r in rows}-modules:raise ValueError('unrequested project declaration module')
    for r in rows:
        if not {'type','explicit_type','axioms'}<=r.keys():raise ValueError('full declaration type/axiom coverage missing')
        if base_rows is not None and (not r.get('kernel_alpha_roundtrip') or 'kernel_type' not in r or not r.get('kernel_dag_roundtrip')):raise ValueError('full kernel explicit type coverage missing')
    old.validate_named_helpers(rows)

def validate_coverage(prior,records,fixtures):
    if len(prior['checks'])!=318 or len(prior['fixture_order'])!=299:raise ValueError('fixed Run19 inventory differs')
    if {r['name'] for r in prior['checks']}-{r['name'] for r in records}:raise ValueError('inherited check coverage missing')
    if set(prior['fixture_order'])-set(fixtures):raise ValueError('inherited fixture coverage missing')
    if len({r['name'] for r in records})!=len(records):raise ValueError('duplicate command identity')

def validate_command_map(prior,records,mapping):
    old={r['name']:r for r in prior['checks']};now={r['name']:r for r in records};mapped={r['name']:r for r in mapping}
    if len(mapped)!=len(mapping) or set(mapped)!=set(now) or not set(old)<=set(mapped):raise ValueError('command map coverage missing/duplicate')
    for name,r in now.items():
        if mapped[name]['new_command']!=r['command'] or mapped[name]['old_command']!=(old[name]['command'] if name in old else None):raise ValueError('command map binding differs: '+name)

def validate_main_type(root,rows):
    expected=json.loads((root/'verification/run20/sources/main_type_fully_explicit.json').read_text())
    actual={r['name']:r for r in rows}
    for name,types in expected.items():
        if name not in actual or any(actual[name].get('pretty_explicit_type' if k=='explicit_type' else k)!=value for k,value in types.items()):raise ValueError('main universal scope/type differs: '+name)

def validate_dependency_map(root,rows):
    path=root/'docs/RUN20_DEPENDENCY_COVERAGE.json';data=json.loads(path.read_text())
    original=json.loads((root/'proof_structure_v3/lemma_registry.json').read_text())['lemmas']
    expected={e['id']:e for e in original};actual={e['id']:e for e in data['entries']}
    if len(actual)!=50 or set(actual)!=set(expected) or len(data['entries'])!=50:raise ValueError('50-ID map coverage differs')
    if data['registry_sha256']!=sha((root/'proof_structure_v3/lemma_registry.json').read_bytes()) or data['required_unproved_inputs']!=[]:raise ValueError('original registry/input scope differs')
    groups={}
    for row in rows:groups.setdefault(row['module'],set()).add(row['name'])
    count=0
    for key,e in actual.items():
        if e['original_statement']!=expected[key]['statement'] or e['original_quantifiers']!=expected[key]['quantifiers']:raise ValueError('original ID meaning changed: '+key)
        if e['status']=='UNDER_REVIEW' or not e['interpretation'] or not e['actual_consumers'] or not e['v06_usage']:raise ValueError('unfinished ID mapping: '+key)
        for g in e['exports']:
            if not g['declarations']:raise ValueError('empty proof group: '+key)
            for name in g['declarations']:
                if not any(n==name or n.endswith('.'+name) for n in groups.get(g['module'],set())):raise ValueError('mapped declaration absent: '+key+' '+g['module']+' '+name)
                count+=1
    return {'original_IDs':50,'mapped_declaration_occurrences':count,'original_statements_and_quantifiers_preserved':True,'necessary_inputs_unproved':[]}

def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--output-dir');p.add_argument('--fresh-project-cache',action='store_true');p.add_argument('--baseline-cache');p.add_argument('--preflight',action='store_true');a=p.parse_args();created=False
    try:
        policy=validate_changes(ROOT,require_new=not a.preflight)
        if a.preflight:print('PASS_RUN20_PREFLIGHT_NOT_CERTIFICATION');return
        if not a.fresh_project_cache:raise ValueError('--fresh-project-cache required')
        rel=a.output_dir or 'verification/run20/runs/release_'+datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%SZ')
        out=validate_output(ROOT,rel);proof=git(ROOT,'rev-parse','HEAD').decode().strip()
        initial=source_manifest(ROOT);check_source_manifest(ROOT,initial,proof)
        prior=json.loads((ROOT/PRIOR/'verification.json').read_text());retained=preserve_evidence(ROOT,out)
        out.mkdir(parents=True,exist_ok=False);created=True;records=[]
        write_json(out/'SOURCE_SHA256.json',initial);write_json(out/'INHERITED_EVIDENCE_SHA256.json',retained)
        snapshot={'proof_snapshot_commit':proof,'base':BASE,'lean':subprocess.check_output(['lean','--version'],text=True).strip(),'mathlib':git(ROOT/'.lake/packages/mathlib','rev-parse','HEAD').decode().strip()}
        snapshot['dependency_sources']=dependency_snapshot(ROOT)
        if 'version 4.36.0-rc2,' not in snapshot['lean'] or snapshot['mathlib']!=v06.MATHLIB:raise ValueError('pin mismatch')
        write_json(out/'snapshot.json',snapshot)
        def invariant():
            if git(ROOT,'rev-parse','HEAD').decode().strip()!=proof:raise ValueError('HEAD changed')
            check_source_manifest(ROOT,initial)
        def run(name,command,cwd=ROOT,compressed=False):
            invariant();start=time.monotonic();q=subprocess.run(command,cwd=cwd,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
            data=q.stdout.encode();(out/(name+('.log.gz' if compressed else '.log'))).write_bytes(gzip.compress(data,mtime=0) if compressed else data)
            ok=q.returncode==0 and not re.search(r'\bwarning:',q.stdout)
            records.append({'name':name,'command':command,'cwd':str(cwd),'exit_code':q.returncode,'passed':ok,'seconds':round(time.monotonic()-start,3)})
            write_json(out/'checks.in_progress.json',records);print(name,q.returncode,'PASS' if ok else 'FAIL',flush=True);invariant()
            if not ok:raise ValueError('check failed: '+name)
            return q.stdout
        backup=Path(tempfile.mkdtemp(prefix='run20-cold-cache-'));moved=[]
        for name in ['.lake/build/lib/lean','.lake/build/ir']:
            source=ROOT/name
            if source.exists():
                dest=backup/name.replace('/','_');shutil.move(str(source),str(dest));moved.append({'from':name,'to':str(dest)})
        write_json(out/'fresh_cache.json',{'whole_project_lib_ir_tests_audits':True,'moved':moved,'fixed_mathlib_cache_retained':True})
        modules=project_modules(ROOT)
        fixtures=v06.fixture_order(ROOT,prior['fixture_order']+sorted(set(policy['new_fixtures'])|set(policy['new_audits'])))
        actual_fixtures={m.replace('.','/')+'.lean' for m in modules if m.startswith(('tests.','audit.'))}
        if set(fixtures)!=actual_fixtures:raise ValueError('whole fixture fileset differs')
        (out/'EnvironmentAudit.lean').write_text(audit_source(modules));mapping=[];raw_environment=None
        old_fixtures={next(s for s in r['command'] if s.endswith('.lean') and s.startswith(('tests/','audit/'))):r for r in prior['checks'] if any(s.endswith('.lean') and s.startswith(('tests/','audit/')) for s in r['command'])}
        for row in prior['checks']:
            name=row['name']
            if any(s.endswith('.lean') and s.startswith(('tests/','audit/')) for s in row['command']):continue
            if name=='build':
                cmd=['lake','build','NSP14','Mathlib.Algebra.Field.ZMod'];run(name,cmd)
                for index,f in enumerate(fixtures):
                    dest=Path('.lake/build/lib/lean')/Path(f).with_suffix('.olean');(ROOT/dest).parent.mkdir(parents=True,exist_ok=True)
                    previous=old_fixtures.get(f);label=previous['name'] if previous else 'run20_fixture_'+str(index).zfill(3)+'_'+Path(f).stem
                    fc=['lake','env','lean','-j1','-M12288',f,'-o',str(dest)];run(label,fc)
                    mapping.append({'name':label,'old_command':previous['command'] if previous else None,'new_command':fc})
            elif name=='environment_axioms':
                cmd=['python3','verification/run20/sources/audit_parts.py','--output-dir',str(Path(rel)/'environment_parts')]
                run(name,cmd)
                raw_environment=(json.loads(gzip.decompress((out/'environment_parts/declarations.json.gz').read_bytes())),
                  json.loads((out/'environment_parts/metadata.json').read_text()))
            elif name in {'base_build','base_environment_types'}:continue
            else:
                cmd=['python3','scripts/replay_run20_inherited.py','--name',name,'--output-dir',str(Path(rel)/('replay_'+name))];run(name,cmd)
            mapping.append({'name':name,'old_command':row['command'],'new_command':cmd})
        # The full immutable base audit was executed read-only with every old
        # module imported all. Reproduce it in a source-checked isolated copy.
        adapter=load('run20_base_prepare',ROOT/'scripts/replay_run19_inherited.py')
        donor=Path(a.baseline_cache) if a.baseline_cache else Path('/tmp/ns-p14-run19-20261116/.lake/build')
        base_files=[n for n in git(ROOT,'ls-tree','-r','--name-only',BASE).decode().splitlines()
          if (n.endswith('.lean') and n.startswith(('NSP14','tests/','audit/'))) or n in ['lean-toolchain','lakefile.toml','lake-manifest.json']]
        donor_present=donor.is_dir()
        if donor_present:
            donor_root=donor.parents[1]
            for name in base_files:
                if not (donor_root/name).is_file() or (donor_root/name).read_bytes()!=git(ROOT,'show',BASE+':'+name):raise ValueError('base cache donor source mismatch: '+name)
        else:
            if a.baseline_cache:raise ValueError('requested baseline cache missing')
            donor=Path(tempfile.mkdtemp(prefix='run20-empty-base-cache-'))
        base=adapter.prepare(ROOT,BASE,ROOT/'.lake/packages',donor)
        try:
            for name in git(ROOT,'ls-tree','-r','--name-only',BASE).decode().splitlines():
                if name.endswith('.lean') and name.startswith(('NSP14','tests/','audit/')) and (base/name).read_bytes()!=git(ROOT,'show',BASE+':'+name):raise ValueError('base donor/source mismatch')
            run('base_build',['lake','build','NSP14','Mathlib.Algebra.Field.ZMod'],cwd=base)
            if not donor_present:
                base_fixtures=v06.fixture_order(base,prior['fixture_order'])
                for ix,f in enumerate(base_fixtures):
                    dest=Path('.lake/build/lib/lean')/Path(f).with_suffix('.olean');(base/dest).parent.mkdir(parents=True,exist_ok=True)
                    run('base_fixture_'+str(ix).zfill(3),['lake','env','lean','-j1','-M12288',f,'-o',str(dest)],cwd=base)
            # Full base audit, not the historical eleven-module V06 subset.
            run('base_environment_types',['python3','verification/run20/sources/audit_parts.py','--source-root',str(base),
              '--output-dir',str(Path(rel)/'base_environment_parts')])
            base_rows=json.loads(gzip.decompress((out/'base_environment_parts/declarations.json.gz').read_bytes()))
            base_meta=json.loads((out/'base_environment_parts/metadata.json').read_text())
            golden=json.loads(gzip.decompress((ROOT/'verification/run20/sources/base_declarations.json.gz').read_bytes()))
            if sorted(base_rows,key=lambda r:r['name'])!=sorted(golden,key=lambda r:r['name']):raise ValueError('full base audit replay differs')
            write_json(out/'base_environment.json',base_meta)
        finally:shutil.rmtree(base)
        rows,meta=raw_environment
        expected_names=json.loads(gzip.decompress((ROOT/'verification/run20/sources/expected_declarations.json.gz').read_bytes()))
        validate_full_audit(rows,meta,modules,base_rows,expected_names);validate_main_type(ROOT,rows)
        write_json(out/'dependency_coverage.json',validate_dependency_map(ROOT,rows))
        for r in rows:r['source_sha256']=initial[r['module'].replace('.','/')+'.lean']
        (out/'declarations.json.gz').write_bytes(gzip.compress(json.dumps(rows,ensure_ascii=False).encode(),mtime=0))
        write_json(out/'environment_import_coverage.json',meta)
        write_json(out/'audit_coverage.json',{'modules':sorted(modules),'declarations':len(rows),'typed_declarations':len(rows),'base_public_types_preserved':True,'private_and_generated_support_included':True,'direct_import_all_for_every_project_module':True,'allowed_axioms':sorted(v06.ALLOWED_AXIOMS),'normal_type':'Lean.Meta.ppExpr default','explicit_type':'Lean.Expr.DAG.v1; all arguments/universes/binder kinds, exact JSON-node reconstruction, unique alpha-normalized binder names; metadata snapshots retained','kernel_alpha_roundtrips':sum(r.get('kernel_alpha_roundtrip') is True for r in rows),'exact_kernel_DAG_roundtrips':sum(r.get('kernel_dag_roundtrip') is True for r in rows),'original_kernel_type_also_recorded':True,'Main_standard_pretty_explicit_also_recorded':True})
        run('run20_inputs',['python3','verification/run20/sources/check_prior_run19.py'])
        run('run20_kernel_encoding_controls',['python3','verification/run20/sources/check_kernel_type_encoding.py','--output-dir',str(Path(rel)/'kernel_encoding_controls')])
        run('run20_routes',['python3','scripts/check_run20_routes.py','--output',str(Path(rel)/'routes.json')])
        run('run20_exact_models',['python3','scripts/check_run20_partition.py','--output',str(Path(rel)/'models.json')])
        run('run20_negative_controls',['python3','scripts/check_run20_guards.py','--output',str(Path(rel)/'guards.json')])
        validate_coverage(prior,records,fixtures);invariant();validate_changes(ROOT)
        if dependency_snapshot(ROOT)!=snapshot['dependency_sources']:raise ValueError('dependency sources changed during validation')
        if preserve_evidence(ROOT,out)!=retained:raise ValueError('inherited evidence bytes/fileset changed')
        # Derive the complete map from the commands that actually executed,
        # including both base checks and all newly added certification checks.
        prior_by_name={r['name']:r for r in prior['checks']}
        mapping=[{'name':r['name'],'old_command':prior_by_name[r['name']]['command'] if r['name'] in prior_by_name else None,
          'new_command':r['command'],'new_cwd':r['cwd'],
          'reason':'current all-project cold check / unique output remap; historical policy scope is recorded by nested replay receipts; Run20 baseline is complete Run19'} for r in records]
        validate_command_map(prior,records,mapping)
        write_json(out/'COMMAND_MAP.json',mapping)
        summary={'status':'PASS_RUN20_COMPLETE_VALIDATION','mathematical_contracts_closed':True,'run20_complete':False,'all_P14_complete':False,
          'completion_pending':['fresh_independent_review','audit_package','normal_push'],'closed_ids':sorted(FULL_IDS),'unproved_ids':[],
          'proof_snapshot_commit':proof,'base':BASE,'evidence_directory':rel,'checks':records,'fixture_order':fixtures,
          'inherited_check_count':318,'inherited_fixture_count':299,'fresh_whole_project_cache':True,'fixed_mathlib_cache_retained':True,
          'normal_explicit_type_and_axiom_coverage':sorted(modules),'environment_declarations':len(rows),'preserved_evidence_count':len(retained),
          'allowed_axioms':sorted(v06.ALLOWED_AXIOMS),'scope':'unconditional all-S all-field all-row P14; actual completed tangent algebras in own minimal variables; literal interval completion'}
        write_json(out/'verification.json',summary);write_json(out/'MANIFEST_SHA256.json',evidence_manifest(ROOT,out))
        print(summary['status'],len(records),'checks',len(fixtures),'fixtures',len(rows),'declarations',flush=True)
    except (ValueError,OSError,subprocess.CalledProcessError,KeyError) as exc:
        if created:write_json(out/'failure.json',{'status':'FAILED_RUN20_ATTEMPT','error':str(exc),'checks':locals().get('records',[])})
        p.exit(1,str(exc)+'\n')
if __name__=='__main__':main()
