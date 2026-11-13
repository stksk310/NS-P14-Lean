#!/usr/bin/env python3
"""Run exact legacy numeric checkers in an isolated root, preserving old evidence."""
from pathlib import Path
import argparse,json,subprocess,sys,tempfile
root=Path(__file__).resolve().parents[1]
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('mode',choices=['coordinates','schedule'])
parser.add_argument('--output',help='fresh JSON output path; default prints only')
args=parser.parse_args();mode=args.mode
destination=Path(args.output)if args.output else None
if destination is not None and destination.exists():parser.error('output already exists; existing evidence is never overwritten')
if mode=='coordinates':
    script='scripts/check_run16_coordinates.py'
    inputs=[]
    output='verification/run16/coordinate_model.json'
elif mode=='schedule':
    script='lean_planning/checks/check_run_schedule_r02.py'
    schedule='lean_planning/run_schedule_r02.json'
    inputs=[schedule,json.loads((root/schedule).read_text())['registry_path']]
    output='lean_planning/run_schedule_r02_check.json'
else:raise SystemExit('expected coordinates or schedule')
before={p:(root/p).read_bytes()for p in [script,*inputs,output]}
with tempfile.TemporaryDirectory(prefix='nsp14-run17-inherited-')as tmp:
    isolated=Path(tmp)
    for rel in [script,*inputs]:
        target=isolated/rel;target.parent.mkdir(parents=True,exist_ok=True)
        target.write_bytes((root/rel).read_bytes())
    (isolated/output).parent.mkdir(parents=True,exist_ok=True)
    subprocess.run([sys.executable,script],cwd=isolated,check=True)
    result=json.loads((isolated/output).read_text())
    expected=json.loads(before[output])
    excluded={'seconds'}if mode=='coordinates'else set()
    assert {k:v for k,v in result.items()if k not in excluded}=={k:v for k,v in expected.items()if k not in excluded}
    if destination is not None:
        destination.parent.mkdir(parents=True,exist_ok=True)
        with destination.open('xb')as f:f.write((isolated/output).read_bytes())
for rel,data in before.items():assert (root/rel).read_bytes()==data,('legacy input/evidence changed',rel)
print('PASS_ISOLATED_LEGACY_REPLAY',mode)
