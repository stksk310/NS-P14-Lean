#!/usr/bin/env python3
"""Run19's own negative controls, in disposable roots. No production axiom is added."""
from pathlib import Path
import argparse, copy, importlib.util, io, json, subprocess, tarfile, tempfile
ROOT=Path(__file__).resolve().parents[1]
def load(name,path):
    spec=importlib.util.spec_from_file_location(name,path);m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m);return m
v=load('run19_guard_verify',ROOT/'scripts/verify_run19.py')
pkg=load('run19_guard_package',ROOT/'scripts/package_run19_audit.py')

def main():
    p=argparse.ArgumentParser();p.add_argument('--output',required=True);a=p.parse_args();output=v.safe(ROOT,a.output)
    if output.exists() or Path(a.output).parts[:3]!=('verification','run19','runs'):p.error('new Run19 output required')
    results=[]
    def reject(name,action,fragment):
        try:action()
        except ValueError as e:
            if fragment not in str(e):raise ValueError(name+': wrong rejection '+str(e))
            results.append({'control':name,'passed':True,'rejection':str(e)})
        else:raise ValueError(name+': invalid input accepted')
    with tempfile.TemporaryDirectory(prefix='run19-controls-') as tmp:
        r=Path(tmp)/'repo'
        subprocess.run(['git','clone','--shared','--no-checkout',str(ROOT),str(r)],check=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
        subprocess.run(['git','read-tree','HEAD'],cwd=r,check=True)
        data=v.git(ROOT,'archive','HEAD')
        with tarfile.open(fileobj=io.BytesIO(data)) as stream:stream.extractall(r,filter='data')
        v.validate_changes(r);results.append({'control':'unaltered_source','passed':True})
        for name in ['/tmp/run19-escape','verification/run19/runs/../escape','verification/run18/runs/old']:
            reject('unsafe_output_'+name,lambda name=name:v.validate_output(r,name),'unsafe relative path' if name.startswith('/') or '..' in name else 'unique verification')
        existing='verification/run19/runs/existing';(r/existing).mkdir(parents=True)
        reject('existing_output',lambda:v.validate_output(r,existing),'already exists')
        alias=r/'verification/run19/runs/alias';alias.symlink_to(r/existing,target_is_directory=True)
        reject('symlink_output',lambda:v.validate_output(r,str(alias.relative_to(r))),'symlink path');alias.unlink()
        for name,label in [('NSP14/Endpoint/CompetitorBounds.lean','inherited_source'),('verification/run18/runs/v06_alignment_20261115T152000Z_r01/verification.json','inherited_evidence')]:
            path=r/name;old=path.read_bytes();path.write_bytes(old+b'\n')
            reject(label,lambda:v.validate_changes(r),'forbidden inherited edit');path.write_bytes(old)
        extra=r/'NSP14/UnlistedRun19Control.lean';extra.write_text('module\n')
        reject('unlisted_source',lambda:v.validate_changes(r),'finite allowlist');extra.unlink()
        manifest=v.source_manifest(r);source=r/'scripts/verify_run19.py';old=source.read_bytes();source.write_bytes(old+b'\n')
        reject('source_substitution',lambda:v.check_source_manifest(r,manifest),'source manifest');source.write_bytes(old)
        ev=r/existing;(ev/'sample').write_text('bound');em=v.evidence_manifest(r,ev);(ev/'sample').write_text('changed')
        reject('evidence_substitution',lambda:v.check_evidence_manifest(r,ev,em),'evidence manifest')
        endpoint='NSP14.Endpoint.CompetitorBounds';fresh='NSP14.SmallEmbedding.LanTuVu'
        rows=[{'name':'Control.old','module':endpoint,'type':'True','explicit_type':'True','axioms':['propext']},
              {'name':'Control.new','module':fresh,'type':'True','explicit_type':'True','axioms':[]}]
        required={endpoint,fresh};v.validate_audit(rows,required,rows)
        reject('changed_old_module_omitted',lambda:v.validate_audit(rows[1:],required),'module type coverage')
        for key in ['type','explicit_type','axioms']:
            bad=copy.deepcopy(rows);del bad[0][key]
            reject('old_declaration_missing_'+key,lambda bad=bad:v.validate_audit(bad,required),'axiom audit coverage' if key=='axioms' else 'module type coverage')
        bad=copy.deepcopy(rows);bad[0]['explicit_type']='False'
        reject('old_public_type_changed',lambda:v.validate_audit(bad,required,rows),'base export type changed')
        bad=copy.deepcopy(rows);bad[1]['axioms']=['Control.badAxiom']
        reject('additional_axiom',lambda:v.validate_audit(bad,required),'unapproved or self axiom')
        reject('helper_omitted',lambda:v.validate_audit(rows[:1],{endpoint},expected_names={r['name'] for r in rows}),'fileset coverage')
        reject('empty_import_missing',lambda:v.validate_import_coverage({'imported_modules':[endpoint]},required),'imported-module coverage')
        prior=json.loads((ROOT/v.PRIOR/'verification.json').read_text())
        v.validate_coverage(prior,prior['checks'],prior['fixture_order'])
        reject('inherited_fixture_omitted',lambda:v.validate_coverage(prior,prior['checks'],prior['fixture_order'][1:]),'fixture coverage')
        for name in ['v06_routes','environment_axioms','base_environment_types']:
            reject('inherited_check_omitted_'+name,lambda name=name:v.validate_coverage(prior,[c for c in prior['checks'] if c['name']!=name],prior['fixture_order']),'check coverage')
    # Exercise the real packager's source/evidence/review Git-byte binding.
    with tempfile.TemporaryDirectory(prefix='run19-package-controls-') as tmp:
        r=Path(tmp)
        def git(*args):return subprocess.check_output(['git',*args],cwd=r,stderr=subprocess.STDOUT).decode().strip()
        def write(n,data):
            path=r/n;path.parent.mkdir(parents=True,exist_ok=True);path.write_text(data)
        def commit(message):
            git('add','-A');git('-c','user.name=Run19 Guard','-c','user.email=guard@example.invalid','commit','-qm',message);return git('rev-parse','HEAD')
        git('init','-q');write('src.lean','-- synthetic publication guard fixture\n');proof=commit('source')
        rel='verification/run19/runs/fixture';out=r/rel;out.mkdir(parents=True)
        summary={'status':'PASS_RUN19_COMPLETE_VALIDATION','unproved_ids':[],'closed_ids':sorted(v.FULL_IDS),'fresh_whole_project_cache':True,
                 'proof_snapshot_commit':proof,'checks':[{'passed':True}]}
        write(rel+'/verification.json',json.dumps(summary));write(rel+'/SOURCE_SHA256.json',json.dumps({'src.lean':v.sha((r/'src.lean').read_bytes())}))
        write(rel+'/MANIFEST_SHA256.json',json.dumps(v.evidence_manifest(r,out)));evidence_commit=commit('evidence')
        report='verification/run19/review/body.md';review='verification/run19/review/review.json'
        write(report,'Synthetic guard body; not a mathematical review.\n')
        receipt={'verdict':'PASS','critical':0,'important':0,'minor':0,'pending':[],'declined':[],'closed_ids':sorted(v.FULL_IDS),
          'source_snapshot_commit':proof,'reviewed_commit':evidence_commit,'review_report':report,'review_report_sha256':v.sha((r/report).read_bytes()),
          'verification_summary_sha256':v.sha((out/'verification.json').read_bytes()),'verification_manifest_sha256':v.sha((out/'MANIFEST_SHA256.json').read_bytes())}
        write(review,json.dumps(receipt));commit('review');pkg.checked_payload(r,rel,review)
        results.append({'control':'valid_synthetic_publication_binding','passed':True})
        for key,value,fragment in [('source_snapshot_commit','0'*40,'review snapshot'),('verification_summary_sha256','0'*64,'review evidence'),('review_report_sha256','0'*64,'review body'),('minor',1,'review gate')]:
            bad=dict(receipt);bad[key]=value;write(review,json.dumps(bad))
            reject('review_mismatch_'+key,lambda:pkg.checked_payload(r,rel,review),fragment)
        write(review,json.dumps(receipt))
        (r/'artifacts').mkdir();archive='artifacts/NS_P14_LEAN_RUN19_guard.zip'
        pkg.package(r,rel,review,archive)
        reject('existing_zip',lambda:pkg.package(r,rel,review,archive),'archive already exists')
    with output.open('x') as stream:json.dump({'status':'PASS_RUN19_NEGATIVE_CONTROLS','count':len(results),'controls':results},stream,indent=2);stream.write('\n')
    print('PASS_RUN19_NEGATIVE_CONTROLS',len(results))
if __name__=='__main__':main()
