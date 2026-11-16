#!/usr/bin/env python3
"""Replay inherited check identities without writing their immutable outputs.

Mathematical models use the current committed source. Historical policy tests
use their own immutable policy snapshot; Run20 has separate current guards.
"""
from pathlib import Path
import argparse, importlib.util, json, shutil, subprocess
ROOT=Path(__file__).resolve().parents[1]
def load(name,path):
    s=importlib.util.spec_from_file_location(name,path);m=importlib.util.module_from_spec(s);s.loader.exec_module(m);return m
old=load('run20_old_replay',ROOT/'scripts/replay_run19_inherited.py')
v=load('run20_replay_verify',ROOT/'scripts/verify_run20.py')

def main():
    p=argparse.ArgumentParser();p.add_argument('--name',required=True);p.add_argument('--output-dir',required=True);a=p.parse_args()
    try:out=v.safe(ROOT,a.output_dir)
    except ValueError as exc:p.error('symlink/escaping replay output forbidden: '+str(exc))
    if out.exists() or Path(a.output_dir).parts[:3]!=('verification','run20','runs'):p.error('new Run20 replay output required')
    prior=json.loads((ROOT/v.PRIOR/'verification.json').read_text())
    row=next(r for r in prior['checks'] if r['name']==a.name)
    policy={'v06_alignment_controls':old.V06_PROOF,'run19_negative_controls':v.UPSTREAM_AUDIT}
    proof=v.git(ROOT,'rev-parse','HEAD').decode().strip();commit=policy.get(a.name,proof)
    scratch=old.prepare(ROOT,commit,ROOT/'.lake/packages',ROOT/'.lake/build')
    try:
        if a.name.startswith('run19_'):
            mapped='verification/run19/runs/run20_disposable'
            command=[s.replace(v.PRIOR,mapped) for s in row['command']]
        else:
            original=json.loads((ROOT/old.PRIOR/'verification.json').read_text())
            row0=next(r for r in original['checks'] if r['name']==a.name)
            mapped='verification/run18/runs/v06_alignment_run20_disposable'
            command=[s.replace(old.PRIOR,mapped) for s in row0['command']]
        (scratch/mapped).mkdir(parents=True,exist_ok=False)
        q=subprocess.run(command,cwd=scratch,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
        out.mkdir(parents=True,exist_ok=False);(out/'process.log').write_text(q.stdout)
        shutil.copytree(scratch/mapped,out/'payload')
        v.write_json(out/'replay.json',{'name':a.name,'old_command':row['command'],'new_command':command,
          'source_commit':commit,'current_mathematical_source':commit==proof,'historical_policy_scope':a.name in policy,
          'independent_git_object_store':True,'exit_code':q.returncode,'old_evidence_written':False})
        print(q.stdout,end='')
        raise SystemExit(q.returncode)
    finally:shutil.rmtree(scratch)
if __name__=='__main__':main()
