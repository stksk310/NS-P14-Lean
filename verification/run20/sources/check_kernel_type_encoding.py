#!/usr/bin/env python3
"""Actual Lean controls for the complete explicit kernel-type representation."""
from pathlib import Path
import argparse,importlib.util,json,subprocess
ROOT=Path(__file__).resolve().parents[3]
s=importlib.util.spec_from_file_location('run20_kernel_controls',ROOT/'scripts/verify_run20.py');v=importlib.util.module_from_spec(s);s.loader.exec_module(v)

def main():
    p=argparse.ArgumentParser();p.add_argument('--output-dir',required=True);a=p.parse_args();out=v.safe(ROOT,a.output_dir)
    if out.exists() or Path(a.output_dir).parts[:3]!=('verification','run20','runs'):p.error('new Run20 control output required')
    out.mkdir(parents=True,exist_ok=False)
    source=v.audit_source({'NSP14.Main'})
    helper=source[source.index('namespace Run20TypeEncoding'):source.index('end Run20TypeEncoding')+len('end Run20TypeEncoding')]
    code='module\nimport Lean\nopen Lean\n'+helper+'''
set_option maxHeartbeats 0
set_option maxRecDepth 4000
#eval show MetaM Unit from do
 let nat := mkConst ``Nat
 let eqxy := mkApp3 (mkConst ``Eq [Level.zero]) nat (mkBVar 1) (mkBVar 0)
 let eqyx := mkApp3 (mkConst ``Eq [Level.zero]) nat (mkBVar 0) (mkBVar 1)
 let mk (a b : Name) (body : Expr) := mkForall a .default nat (mkForall b .default nat body)
 let first := mk `x `y eqxy
 let renamed := mk `other `last eqxy
 let swapped := mk `x `y eqyx
 let norm (e : Expr) := Run20TypeEncoding.canonical 0 e
 unless norm first == first do throwError "alpha equivalence lost"
 unless (toString (norm first)) == toString (norm renamed) do throwError "alpha names not canonical"
 if (toString (norm first)) == toString (norm swapped) then throwError "bound-variable indices collapsed"
 let explicit := mkForall `x .default nat (mkBVar 0)
 let implicit := mkForall `x .implicit nat (mkBVar 0)
 let instanceBinder := mkForall `x .instImplicit nat (mkBVar 0)
 if (toString (norm explicit)) == toString (norm implicit) then throwError "implicit binder collapsed"
 if (toString (norm implicit)) == toString (norm instanceBinder) then throwError "instance binder collapsed"
 if toString (norm (.sort Level.zero)) == toString (norm (.sort (.succ Level.zero))) then throwError "universes collapsed"
 unless norm (.mdata {} first) == .mdata {} first do throwError "metadata was not preserved"
 let mut deep := mkNatLit 0
 for _ in [:200] do deep := mkApp (mkConst ``Nat.succ) deep
 let raw := toString (norm deep)
 unless (raw.splitOn "Nat.succ").length==201 do throwError "deep kernel term was elided"
 if raw.contains '⋯' || raw.contains '…' then throwError "kernel display omission"
 let controls := #["actual alpha-equivalence", "binder renaming", "bound-variable order",
   "explicit/implicit binder", "instance binder", "universe levels", "exact metadata preservation",
   "all 200 nested applications", "no display ellipses"]
 IO.println ((Json.mkObj [("status",toJson "PASS_COMPLETE_KERNEL_TYPE_ENCODING"),("controls",toJson controls)]).compress)
'''
    path=out/'Controls.lean';path.write_text(code);command=['lake','env','lean','-j1','-M12288',str(path)]
    q=subprocess.run(command,cwd=ROOT,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT);(out/'Controls.log').write_text(q.stdout)
    if q.returncode or 'warning:' in q.stdout:raise ValueError('kernel encoding control failed: '+q.stdout)
    result=json.loads(next(line for line in q.stdout.splitlines() if line.startswith('{')))
    v.write_json(out/'result.json',{**result,'command':command,'exit_code':q.returncode,'source_sha256':v.sha(path.read_bytes())})
    print(result['status'],len(result['controls']))
if __name__=='__main__':main()
