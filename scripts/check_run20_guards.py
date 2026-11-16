#!/usr/bin/env python3
"""Run20's own negative controls, in disposable roots. No production axiom is added."""
from pathlib import Path
import argparse, copy, importlib.util, io, json, subprocess, tarfile, tempfile
ROOT=Path(__file__).resolve().parents[1]
def load(name,path):
    spec=importlib.util.spec_from_file_location(name,path);m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m);return m
v=load('run20_guard_verify',ROOT/'scripts/verify_run20.py')
pkg=load('run20_guard_package',ROOT/'scripts/package_run20_audit.py')

def main():
    p=argparse.ArgumentParser();p.add_argument('--output',required=True);a=p.parse_args();output=v.safe(ROOT,a.output)
    if output.exists() or Path(a.output).parts[:3]!=('verification','run20','runs'):p.error('new Run20 output required')
    results=[]
    def reject(name,action,fragment):
        try:action()
        except ValueError as e:
            if fragment not in str(e):raise ValueError(name+': wrong rejection '+str(e))
            results.append({'control':name,'passed':True,'rejection':str(e)})
        else:raise ValueError(name+': invalid input accepted')
    with tempfile.TemporaryDirectory(prefix='run20-controls-') as tmp:
        r=Path(tmp)/'repo'
        subprocess.run(['git','clone','--shared','--dissociate','--no-checkout',str(ROOT),str(r)],check=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
        subprocess.run(['git','read-tree','HEAD'],cwd=r,check=True)
        data=v.git(ROOT,'archive','HEAD')
        with tarfile.open(fileobj=io.BytesIO(data)) as stream:stream.extractall(r,filter='data')
        v.validate_changes(r);results.append({'control':'unaltered_source','passed':True})
        for name in ['/tmp/run20-escape','verification/run20/runs/../escape','verification/run19/runs/old']:
            reject('unsafe_output_'+name,lambda name=name:v.validate_output(r,name),'unsafe relative path' if name.startswith('/') or '..' in name else 'unique verification')
        existing='verification/run20/runs/existing';(r/existing).mkdir(parents=True)
        reject('existing_output',lambda:v.validate_output(r,existing),'already exists')
        alias=r/'verification/run20/runs/alias';alias.symlink_to(r/existing,target_is_directory=True)
        reject('symlink_output',lambda:v.validate_output(r,str(alias.relative_to(r))),'symlink path')
        probe=subprocess.run(['python3',str(r/'scripts/replay_run20_inherited.py'),'--name','width_model',
            '--output-dir','verification/run20/runs/alias/escape'],cwd=r,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
        if probe.returncode!=2 or 'symlink/escaping' not in probe.stdout:raise ValueError('replay symlink output was not rejected')
        results.append({'control':'replay_symlink_output','passed':True});alias.unlink()
        for name,label in [('NSP14/Endpoint/CompetitorBounds.lean','inherited_source'),('verification/run19/runs/release_20261116_r03/verification.json','inherited_evidence')]:
            path=r/name;old=path.read_bytes();path.write_bytes(old+b'\n')
            reject(label,lambda:v.validate_changes(r),'forbidden inherited edit');path.write_bytes(old)
        extra=r/'NSP14/UnlistedRun20Control.lean';extra.write_text('module\n')
        reject('unlisted_source',lambda:v.validate_changes(r),'finite allowlist');extra.unlink()
        manifest=v.source_manifest(r);source=r/'scripts/verify_run20.py';old=source.read_bytes();source.write_bytes(old+b'\n')
        reject('source_substitution',lambda:v.check_source_manifest(r,manifest),'source manifest');source.write_bytes(old)
        helper=r/'verification/run20/sources/check_prior_run19.py';old=helper.read_bytes();helper.write_bytes(old+b'\n')
        reject('auxiliary_checker_substitution',lambda:v.check_source_manifest(r,manifest),'source manifest');helper.write_bytes(old)
        helper=r/'verification/run20/sources/audit_parts.py';old=helper.read_bytes();helper.write_bytes(old+b'\n')
        reject('parallel_audit_helper_substitution',lambda:v.check_source_manifest(r,manifest),'source manifest');helper.write_bytes(old)
        ev=r/existing;(ev/'sample').write_text('bound');em=v.evidence_manifest(r,ev);(ev/'sample').write_text('changed')
        reject('evidence_substitution',lambda:v.check_evidence_manifest(r,ev,em),'evidence manifest')
        endpoint='NSP14.Endpoint.CompetitorBounds';fresh='NSP14.SmallEmbedding.LanTuVu'
        rows=[{'name':'Control.old','module':endpoint,'type':'True','explicit_type':'True','axioms':['propext']},
              {'name':'Control.new','module':fresh,'type':'True','explicit_type':'True','axioms':[]}]
        required={endpoint,fresh};v.v06.validate_audit(rows,required,rows)
        reject('changed_old_module_omitted',lambda:v.v06.validate_audit(rows[1:],required),'module type coverage')
        for key in ['type','explicit_type','axioms']:
            bad=copy.deepcopy(rows);del bad[0][key]
            reject('old_declaration_missing_'+key,lambda bad=bad:v.v06.validate_audit(bad,required),'axiom audit coverage' if key=='axioms' else 'module type coverage')
        bad=copy.deepcopy(rows);bad[0]['explicit_type']='False'
        reject('old_public_type_changed',lambda:v.v06.validate_audit(bad,required,rows),'base export type changed')
        bad=copy.deepcopy(rows);bad[1]['axioms']=['Control.badAxiom']
        reject('additional_axiom',lambda:v.v06.validate_audit(bad,required),'unapproved or self axiom')
        reject('helper_omitted',lambda:v.v06.validate_audit(rows[:1],{endpoint},expected_names={r['name'] for r in rows}),'fileset coverage')
        helpers=[{'module':m,'name':prefix+'.'+n,'type':'True','explicit_type':'True','axioms':[]}
          for m,(prefix,names) in v.old.FIXTURE_HELPERS.items() for n in names]
        v.old.validate_named_helpers(helpers)
        reject('named_helper_omitted_despite_other_module_rows',lambda:v.old.validate_named_helpers(helpers[1:]),'named fixture helper coverage')
        audit=v.audit_source(required)
        if any('import all '+m+'\n' not in audit for m in required):raise ValueError('private module import coverage missing')
        results.append({'control':'each_typed_module_imported_all_directly','passed':True})
        all_rows=helpers+rows
        modules={x['module'] for x in all_rows}
        meta={'imported_modules':sorted(modules),'declaration_inventory':[x['name'] for x in all_rows]}
        v.validate_full_audit(all_rows,meta,modules)
        reject('single_private_name_omitted_with_module_remaining',lambda:v.validate_full_audit(all_rows[1:],meta,modules),'fileset coverage')
        reduced=copy.deepcopy(meta);reduced['declaration_inventory']=reduced['declaration_inventory'][1:]
        reject('private_name_omitted_from_both_rows_and_metadata',lambda:v.validate_full_audit(all_rows[1:],reduced,modules,expected_names=meta['declaration_inventory']),'frozen declaration-name coverage')
        kernel_rows=[{**r,'kernel_type':'Sort 0','kernel_alpha_roundtrip':True} for r in all_rows]
        v.validate_full_audit(kernel_rows,meta,modules,base_rows=[])
        bad=copy.deepcopy(kernel_rows);del bad[0]['kernel_type']
        reject('complete_kernel_type_omitted',lambda:v.validate_full_audit(bad,meta,modules,base_rows=[]),'kernel explicit type coverage')
        bad=copy.deepcopy(kernel_rows);bad[0]['kernel_alpha_roundtrip']=False
        reject('kernel_alpha_roundtrip_failed',lambda:v.validate_full_audit(bad,meta,modules,base_rows=[]),'kernel explicit type coverage')
        batch=load('run20_guard_parts',ROOT/'verification/run20/sources/audit_parts.py')
        pair=[{'selected_modules':[x['module']],'rows':[x],'metadata':{'imported_modules':sorted(required),'declaration_inventory':[x['name']]}} for x in rows]
        batch.validate_parts(pair,required)
        reject('audit_part_omitted',lambda:batch.validate_parts(pair[:1],required),'part module coverage')
        reject('audit_part_duplicated',lambda:batch.validate_parts(pair+pair[:1],required),'duplicate part module coverage')
        changed=copy.deepcopy(all_rows);del changed[0]['explicit_type']
        reject('private_explicit_type_omitted',lambda:v.validate_full_audit(changed,meta,modules),'coverage')
        wrong=copy.deepcopy(meta);wrong['imported_modules']=wrong['imported_modules'][1:]
        reject('whole_project_import_omitted',lambda:v.validate_full_audit(all_rows,wrong,modules),'imported-module coverage')
        main=json.loads((r/'verification/run20/sources/main_type_fully_explicit.json').read_text())
        scope_rows=[{'name':n,'type':types['type'],'pretty_explicit_type':types['explicit_type']} for n,types in main.items()]
        v.validate_main_type(r,scope_rows)
        scope_rows[0]['type']='forall S k, i <= S.embeddingDimension -> True'
        reject('main_scope_shrunk',lambda:v.validate_main_type(r,scope_rows),'universal scope/type')
        for target,label in [('audit/run20/RequestedGoals.lean','frozen_scope'),('audit/run20/acceptance/I_MAIN.lean','frozen_acceptance')]:
            f=r/target;data=f.read_bytes();f.write_bytes(data+b'\n')
            reject(label,lambda:v.validate_changes(r),'frozen contract');f.write_bytes(data)
        reject('empty_import_missing' ,lambda:v.v06.validate_import_coverage({'imported_modules':[endpoint]},required),'imported-module coverage')
        prior=json.loads((ROOT/v.PRIOR/'verification.json').read_text())
        v.validate_coverage(prior,prior['checks'],prior['fixture_order'])
        reject('inherited_fixture_omitted',lambda:v.validate_coverage(prior,prior['checks'],prior['fixture_order'][1:]),'fixture coverage')
        for name in ['v06_routes','environment_axioms','base_environment_types','run19_routes','run19_negative_controls']:
            reject('inherited_check_omitted_'+name,lambda name=name:v.validate_coverage(prior,[c for c in prior['checks'] if c['name']!=name],prior['fixture_order']),'check coverage')
        cmap=[{'name':row['name'],'old_command':row['command'],'new_command':row['command']} for row in prior['checks']]
        v.validate_command_map(prior,prior['checks'],cmap)
        reject('command_mapping_omitted',lambda:v.validate_command_map(prior,prior['checks'],cmap[1:]),'command map coverage')
        badmap=copy.deepcopy(cmap);badmap[0]['new_command']=['false']
        reject('command_mapping_substituted',lambda:v.validate_command_map(prior,prior['checks'],badmap),'command map binding')
        table=r/'docs/RUN20_DEPENDENCY_COVERAGE.json';table_bytes=table.read_bytes();coverage=json.loads(table_bytes)
        mapped=[{'module':g['module'],'name':g['module']+'.'+n} for entry in coverage['entries'] for g in entry['exports'] for n in g['declarations']]
        v.validate_dependency_map(r,mapped)
        bad=copy.deepcopy(coverage);bad['entries']=bad['entries'][1:];table.write_text(json.dumps(bad))
        reject('original_ID_omitted',lambda:v.validate_dependency_map(r,mapped),'50-ID map coverage')
        bad=copy.deepcopy(coverage);bad['entries'][0]['original_quantifiers']='only characteristic zero';table.write_text(json.dumps(bad))
        reject('original_ID_quantifiers_changed',lambda:v.validate_dependency_map(r,mapped),'original ID meaning')
        table.write_bytes(table_bytes)
        # Actual Lean collectAxioms on an isolated injected axiom. It is never
        # imported into production or the project environment being certified.
        probe=r/'Run20NegativeAxiom.lean';probe.write_text('''import Lean
axiom Run20Negative.bad : False
theorem Run20Negative.consumer : False := Run20Negative.bad
#eval show Lean.MetaM Unit from do
 let axs ← Lean.collectAxioms `Run20Negative.consumer
 IO.println ((Lean.Json.mkObj [("axioms", Lean.toJson (axs.map Lean.Name.toString))]).compress)
''')
        command=['lake','env','lean','-j1','-M12288',str(probe)]
        process=subprocess.run(command,cwd=ROOT,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
        if process.returncode or 'warning:' in process.stdout:raise ValueError('actual axiom probe failed to execute: '+process.stdout)
        actual=json.loads(next(line for line in process.stdout.splitlines() if line.startswith('{')))
        row={'name':'Run20Negative.consumer','module':'Run20Negative','type':'False','explicit_type':'False','axioms':actual['axioms']}
        reject('real_lean_additional_axiom',lambda:v.v06.validate_audit([row],{'Run20Negative'}),'unapproved or self axiom')
        results[-1]['command']=command;results[-1]['raw_output']=process.stdout
    # Exercise the real packager's source/evidence/review Git-byte binding.
    with tempfile.TemporaryDirectory(prefix='run20-package-controls-') as tmp:
        r=Path(tmp)
        def git(*args):return subprocess.check_output(['git',*args],cwd=r,stderr=subprocess.STDOUT).decode().strip()
        def write(n,data):
            path=r/n;path.parent.mkdir(parents=True,exist_ok=True);path.write_text(data)
        def commit(message):
            git('add','-A');git('-c','user.name=Run20 Guard','-c','user.email=guard@example.invalid','commit','-qm',message);return git('rev-parse','HEAD')
        git('init','-q');write('src.lean','-- synthetic publication guard fixture\n')
        helper='verification/run20/sources/probe.py';write(helper,"print('synthetic helper')\n");proof=commit('source')
        rel='verification/run20/runs/fixture';out=r/rel;out.mkdir(parents=True)
        summary={'status':'PASS_RUN20_COMPLETE_VALIDATION','unproved_ids':[],'closed_ids':sorted(v.FULL_IDS),'fresh_whole_project_cache':True,
                 'proof_snapshot_commit':proof,'checks':[{'passed':True}]}
        write(rel+'/verification.json',json.dumps(summary));write(rel+'/SOURCE_SHA256.json',json.dumps(v.source_manifest(r)))
        write(rel+'/MANIFEST_SHA256.json',json.dumps(v.evidence_manifest(r,out)));evidence_commit=commit('evidence')
        report='verification/run20/review/body.md';review='verification/run20/review/review.json'
        write(report,'Synthetic guard body; not a mathematical review.\n')
        receipt={'verdict':'PASS','critical':0,'important':0,'minor':0,'pending':[],'declined':[],'closed_ids':sorted(v.FULL_IDS),
          'source_snapshot_commit':proof,'reviewed_commit':evidence_commit,'review_report':report,'review_report_sha256':v.sha((r/report).read_bytes()),
          'verification_summary_sha256':v.sha((out/'verification.json').read_bytes()),'verification_manifest_sha256':v.sha((out/'MANIFEST_SHA256.json').read_bytes())}
        write(review,json.dumps(receipt));commit('review');pkg.checked_payload(r,rel,review)
        results.append({'control':'valid_synthetic_publication_binding','passed':True})
        original=(r/helper).read_bytes();(r/helper).write_bytes(original+b'\n')
        reject('packager_auxiliary_checker_substitution',lambda:pkg.checked_payload(r,rel,review),'source manifest');(r/helper).write_bytes(original)
        for key,value,fragment in [('source_snapshot_commit','0'*40,'review snapshot'),('verification_summary_sha256','0'*64,'review evidence'),('review_report_sha256','0'*64,'review body'),('minor',1,'review gate')]:
            bad=dict(receipt);bad[key]=value;write(review,json.dumps(bad))
            reject('review_mismatch_'+key,lambda:pkg.checked_payload(r,rel,review),fragment)
        write(review,json.dumps(receipt))
        (r/'artifacts').mkdir();archive='artifacts/NS_P14_LEAN_RUN20_guard.zip'
        pkg.package(r,rel,review,archive)
        reject('existing_zip',lambda:pkg.package(r,rel,review,archive),'archive already exists')
    with output.open('x') as stream:json.dump({'status':'PASS_RUN20_NEGATIVE_CONTROLS','count':len(results),'controls':results},stream,indent=2);stream.write('\n')
    print('PASS_RUN20_NEGATIVE_CONTROLS',len(results))
if __name__=='__main__':main()
