#!/usr/bin/env python3
"""Replay unchanged historical checkers in disposable roots, never old evidence.

The V06 policy controls test the immutable V06 policy at its own proof snapshot;
all mathematical models, Lean probes and fixtures use the current Run19 source.
This distinction is recorded rather than relaxing an old allowlist.
"""
from pathlib import Path
import argparse, io, json, shutil, subprocess, tarfile, tempfile

ROOT = Path(__file__).resolve().parents[1]
PRIOR = 'verification/run18/runs/v06_alignment_20261115T152000Z_r01'
V06_PROOF = 'd446fc2f18f7a8603d1eedd446e93810dc44d01c'

def prepare(root, commit, packages, build):
    scratch = Path(tempfile.mkdtemp(prefix='nsp14-run19-replay-'))
    subprocess.run(['git', 'clone', '--shared', '--dissociate', '--no-checkout', str(root), str(scratch)],
                   check=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    alternates=scratch/'.git/objects/info/alternates'
    if alternates.exists() and alternates.read_text().strip():
        raise ValueError('isolated replay still borrows a nested object store')
    subprocess.run(['git', 'update-ref', '--no-deref', 'HEAD', commit], cwd=scratch, check=True)
    subprocess.run(['git', 'read-tree', commit], cwd=scratch, check=True)
    archive = subprocess.check_output(['git', 'archive', commit], cwd=root)
    with tarfile.open(fileobj=io.BytesIO(archive)) as stream:
        stream.extractall(scratch, filter='data')
    (scratch / '.lake').mkdir(exist_ok=True)
    (scratch / '.lake/packages').symlink_to(packages.resolve(), target_is_directory=True)
    # Copy project cache: probes may create adjacent outputs; donor is never changed.
    shutil.copytree(build, scratch / '.lake/build', symlinks=True)
    return scratch

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--name', required=True); p.add_argument('--output-dir', required=True)
    a=p.parse_args(); out=ROOT/a.output_dir
    rel=Path(a.output_dir)
    if rel.is_absolute() or '..' in rel.parts or rel.parts[:3]!=('verification','run19','runs') or out.exists():
        p.error('new exclusive Run19 output required')
    if (not out.resolve().is_relative_to(ROOT.resolve()) or
        any(part.is_symlink() for part in [out,*out.parents] if part.is_relative_to(ROOT))):
        p.error('symlink/escaping replay output forbidden')
    prior=json.loads((ROOT/PRIOR/'verification.json').read_text())
    row=next(r for r in prior['checks'] if r['name']==a.name)
    proof=subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip()
    commit=V06_PROOF if a.name=='v06_alignment_controls' else proof
    scratch=prepare(ROOT,commit,ROOT/'.lake/packages',ROOT/'.lake/build')
    try:
        mapped='verification/run18/runs/v06_alignment_run19_disposable'
        (scratch/mapped).mkdir(parents=True,exist_ok=False)
        command=[arg.replace(PRIOR,mapped) for arg in row['command']]
        result=subprocess.run(command,cwd=scratch,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
        out.mkdir(parents=True,exist_ok=False)
        (out/'process.log').write_text(result.stdout)
        shutil.copytree(scratch/mapped,out/'payload')
        receipt={'name':a.name,'old_command':row['command'],'new_command':command,
          'source_commit':commit,'current_mathematical_source':commit==proof,
          'policy_control_at_its_original_snapshot':a.name=='v06_alignment_controls',
          'independent_git_object_store':True,
          'exit_code':result.returncode,'scratch':str(scratch),'old_evidence_written':False}
        (out/'replay.json').write_text(json.dumps(receipt,indent=2)+'\n')
        print(result.stdout,end='')
        if result.returncode:raise SystemExit(result.returncode)
    finally:shutil.rmtree(scratch)

if __name__=='__main__':main()
