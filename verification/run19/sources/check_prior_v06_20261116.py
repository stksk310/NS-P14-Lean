#!/usr/bin/env python3
import hashlib,json,pathlib,subprocess,zipfile
r=pathlib.Path(__file__).resolve().parents[3]
sha=lambda b:hashlib.sha256(b).hexdigest()
git=lambda *a:subprocess.check_output(['git',*a],cwd=r)
v=r/'verification/run18/runs/v06_alignment_20261115T152000Z_r01'
s=json.loads((v/'verification.json').read_text());assert s['status']=='V06_ALIGNMENT_COMPLETE' and len(s['checks'])==289 and s['fixture_count']==273 and all(x['passed'] and x['exit_code']==0 for x in s['checks'])
source=json.loads((v/'SOURCE_SHA256.json').read_text());ev=json.loads((v/'MANIFEST_SHA256.json').read_text())
for n,h in source.items():assert sha(git('show',s['proof_snapshot_commit']+':'+n))==h,n
for n,h in ev.items():assert sha((r/n).read_bytes())==h,n
for n,h in json.loads((v/'INHERITED_EVIDENCE_SHA256.json').read_text()).items():assert sha((r/n).read_bytes())==h,n
for n in source:
 if n.endswith('.lean') or n.startswith('scripts/') or n in ['lean-toolchain','lake-manifest.json','lakefile.toml']:assert sha((r/n).read_bytes())==source[n],n
with zipfile.ZipFile(r/'artifacts/NS_P14_V06_ALIGNMENT_20261116_R01.zip') as z:
 assert z.testzip() is None
 m=json.loads(z.read('BUNDLE_SHA256.json'));assert set(z.namelist())==set(m)|{'BUNDLE_SHA256.json'}
 for n,h in m.items():assert sha(z.read(n))==h,n
assert sha((r/'proof_sharp_v6/chapters/05_N4_JA.md').read_bytes())=='cd6236f6b16d5de7998064e66d566f5c6522c8a943d040ec6242a18dde2194c5'
assert sha((r/'proof_sharp_v6/NS_P14_SHARP_V06.zip').read_bytes())=='788e4c75c572af8a09fc14de5327417b584b7d3b5725d6496bb9445e2c331f4d'
print(json.dumps(dict(status='PASS_PRIOR_V06_AND_RUN19_INPUTS',proof=s['proof_snapshot_commit'],evidence='0880f6f30836873036b4d9908b7dcef50125d2c8',checks=289,fixtures=273,source_files=len(source),evidence_files=len(ev),n4_and_zip_hashes=True,core_math_source_identical=True),indent=2))
