#!/usr/bin/env python3
"""Actual-Lean controls: accept a proved module-interface stub, reject a genuine extra axiom."""
from pathlib import Path
import argparse,importlib.util,json,subprocess
ROOT=Path(__file__).resolve().parents[1]
spec=importlib.util.spec_from_file_location('run18_verify',ROOT/'scripts/verify_run18.py')
verify=importlib.util.module_from_spec(spec);spec.loader.exec_module(verify)
def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--output-dir',required=True);a=p.parse_args()
    rel=Path(a.output_dir)
    if rel.is_absolute()or'..'in rel.parts or rel.parts[:2]!=('verification','run18'):p.error('new output directory under verification/run18 required')
    out=ROOT/rel
    if out.exists():p.error('output directory exists')
    out.mkdir(parents=True,exist_ok=False)
    probe=out/'ExtraAxiomProbe.lean'
    probe.write_text('''module
import NSP14.Ordinary.Scalarization
import Lean
open Lean
-- NEGATIVE CONTROL ONLY. This file is never imported by production, fixtures or the main environment audit.
-- The declaration below must be rejected; it is not a dependency of any project proof.
axiom Run18AxiomPolicyProbe.extra : True
#eval show MetaM Unit from do
 for n in [``NSP14.Ordinary.Scalarization.weight_head_le, ``Run18AxiomPolicyProbe.extra] do
  let ci ← getConstInfo n
  let kind := match ci with
   | .axiomInfo _ => "axiom"
   | .thmInfo _ => "theorem"
   | _ => "other"
  let axs ← collectAxioms n
  IO.println ((Json.mkObj [("name",toJson n.toString),("kind",toJson kind),
   ("axioms",toJson (axs.map Name.toString))]).compress)
''')
    r=subprocess.run(['lake','env','lean','-j1','-M4096',str(probe.relative_to(ROOT))],cwd=ROOT,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
    (out/'probe.log').write_text(r.stdout)
    assert r.returncode==0 and 'warning:'not in r.stdout,r.stdout
    rows=[json.loads(l)for l in r.stdout.splitlines()if l.startswith('{')]
    assert len(rows)==2
    stub,extra=rows
    assert stub['kind']=='axiom'and verify.validated_kind(stub)=='exported_proof_stub',stub
    assert extra['name']in extra['axioms']and extra['kind']=='axiom',extra
    try:verify.validated_kind(extra)
    except ValueError:pass
    else:raise AssertionError('genuine extra axiom was accepted')
    result=dict(status='PASS_ACTUAL_LEAN_AXIOM_POLICY_CONTROLS',accepted_proven_interface_stub=stub,
        rejected_test_only_extra_axiom=extra,production_depends_on_negative_control=False)
    (out/'result.json').write_text(json.dumps(result,indent=2)+'\n')
    print(result['status'])
if __name__=='__main__':main()
