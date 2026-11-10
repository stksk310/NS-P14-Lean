#!/usr/bin/env python3
"""Independently collect current explicit types for all 49 Run14 core modules."""
from pathlib import Path
import gzip
import json
import subprocess

root = Path(__file__).resolve().parents[2]
out = root/'audit/block14'
sources = subprocess.check_output(['git', 'diff', '--name-only', 'd8556dc', 'fbfa5de', '--', 'NSP14'],
                                  cwd=root, text=True).splitlines()
modules = [p[:-5].replace('/', '.') for p in sources]
lean = '''module
import NSP14
import Lean
open Lean
set_option maxRecDepth 4000
set_option maxHeartbeats 0
#eval show MetaM Unit from do
 let env ← getEnv
 let included : Array String := #['''+','.join(json.dumps(m) for m in modules)+''']
 for (n, ci) in env.constants.toList do
  let some idx := env.getModuleIdxFor? n | continue
  let modName := env.header.moduleNames[idx.toNat]!.toString
  if included.contains modName then
   let axs ← collectAxioms n
   let tp ← Meta.ppExpr ci.type
   let ep ← withOptions (fun o => o.setBool `pp.explicit true) (Meta.ppExpr ci.type)
   IO.println ((Json.mkObj [("name", toJson n.toString), ("module", toJson modName),
     ("type", toJson tp.pretty), ("explicit_type", toJson ep.pretty),
     ("axioms", toJson (axs.map Name.toString))]).compress)
'''
(out/'CoreTypes.lean').write_text(lean)
r = subprocess.run(['lake', 'env', 'lean', 'audit/block14/CoreTypes.lean'], cwd=root,
                   text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
(out/'core_types.log.gz').write_bytes(gzip.compress(r.stdout.encode(), mtime=0))
assert r.returncode == 0 and 'warning:' not in r.stdout, r.stdout[:4000]
rows = [json.loads(x) for x in r.stdout.splitlines() if x.startswith('{')]
assert len(rows) == len({x['name'] for x in rows}) == 699
assert {x['module'] for x in rows} == set(modules)
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
for x in rows:
    assert set(x['axioms']) <= allowed and x['name'] not in x['axioms'], x['name']
initial = json.loads((root/'verification/run14/declarations.json').read_text())
final = json.loads(gzip.decompress((root/'verification/run14_continuation/declarations.json.gz').read_bytes()))
expected = {x['name']: x for x in initial+final if 'explicit_type' in x and
            x['source'] in sources}
assert set(expected) == {x['name'] for x in rows}
for x in rows:
    y = expected[x['name']]
    for key in ['module', 'type', 'explicit_type']:
        assert x[key] == y[key], (x['name'], key)
    assert set(x['axioms']) == set(y['axioms']), x['name']
(out/'core_types.json.gz').write_bytes(gzip.compress(
    (json.dumps(sorted(rows, key=lambda x: x['name']), indent=2)+'\n').encode(), mtime=0))
(out/'core_type_check.json').write_text(json.dumps(dict(status='PASS', core_modules=49,
    current_environment_declarations=699, explicit_types_and_axioms_match_submission=True), indent=2)+'\n')
print('PASS: 699 core declaration types and axioms across all 49 Run14 modules')
