#!/usr/bin/env python3
"""Negative control for Lean's imported, proof-erased module axiom metadata.

An intentionally invalid dependency is generated only in a temporary directory;
it is never imported by NSP14 or the acceptance/replay modules.
"""
from pathlib import Path
import json
import os
import subprocess
import tempfile

root = Path(__file__).resolve().parents[2]
env = os.environ.copy()
lake_path = subprocess.check_output(['lake', 'env', 'printenv', 'LEAN_PATH'], cwd=root, text=True).strip()
with tempfile.TemporaryDirectory(prefix='run13-axiom-probe-') as td:
    temp = Path(td)
    env['LEAN_PATH'] = td + os.pathsep + lake_path
    probe = temp/'Run13AxiomProbe.lean'
    probe.write_text('''module
public import Lean
@[expose] public section
namespace IsolatedAuditProbe
axiom sentinel : True
theorem bad : True := sentinel
theorem good : True := True.intro
end IsolatedAuditProbe
''')
    subprocess.run(['lean', '--root='+td, str(probe), '-o', str(probe.with_suffix('.olean'))],
                   env=env, cwd=root, check=True, capture_output=True, text=True)
    check = temp/'Check.lean'
    check.write_text('''module
import Run13AxiomProbe
open Lean
#eval show MetaM Unit from do
  for n in #[`IsolatedAuditProbe.sentinel, `IsolatedAuditProbe.bad, `IsolatedAuditProbe.good] do
    let axs ← collectAxioms n
    IO.println ((Json.mkObj [("name", toJson n.toString),
      ("axioms", toJson (axs.map Name.toString))]).compress)
''')
    r = subprocess.run(['lean', str(check)], env=env, cwd=root,
                       check=True, capture_output=True, text=True)
    assert not r.stderr and 'warning:' not in r.stdout
    rows = [json.loads(s) for s in r.stdout.splitlines() if s.startswith('{')]
    allowed = {'propext', 'Classical.choice', 'Quot.sound'}
    assert len(rows) == 3
    for row in rows:
        accepted = set(row['axioms']) <= allowed and row['name'] not in row['axioms']
        assert accepted == row['name'].endswith('.good'), row
        row['accepted_by_release_rule'] = accepted
    result = dict(status='PASS', isolated_temporary_negative_control=True, declarations=rows)
    (root/'audit/block13/axiom_detector.json').write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps(result, indent=2))
