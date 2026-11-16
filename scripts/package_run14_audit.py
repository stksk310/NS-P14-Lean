#!/usr/bin/env python3
"""Package verified partial Run14 evidence without certifying Run14 completion."""
from pathlib import Path
import hashlib,json,subprocess,zipfile
root=Path(__file__).resolve().parents[1]
v=json.loads((root/'verification/run14/verification.json').read_text())
s=json.loads((root/'docs/RUN14_CLOSURE_STATUS.json').read_text())
assert v['status']=='PASS_IMPLEMENTED_EXPORTS_ONLY'
assert s['status']=='PARTIAL_NOT_RUN14_COMPLETE'
for p,h in json.loads((root/'verification/run14/SOURCE_SHA256.json').read_text()).items():
 assert hashlib.sha256((root/p).read_bytes()).hexdigest()==h,p
files=set(subprocess.check_output(['git','ls-files','-z'],cwd=root).decode().split('\0'))
files.update(subprocess.check_output(['git','ls-files','--others','--exclude-standard','-z'],cwd=root).decode().split('\0'))
allowed={'NSP14','tests','docs','verification','audit','scripts','lean_planning','.github'}
rootfiles={'NSP14.lean','README.md','AUDIT_HANDOFF.md','LEAN_PROGRESS.md','lean-toolchain','lakefile.toml','lake-manifest.json','.gitignore'}
payload={}
for p in sorted(files):
 pp=Path(p)
 if not p or not (pp.parts[0] in allowed or p in rootfiles):continue
 path=root/p
 if not path.is_file() or path.suffix in {'.zip','.olean','.ilean','.pyc'}:continue
 payload[p]=path.read_bytes()
manifest={p:hashlib.sha256(b).hexdigest() for p,b in payload.items()}
a=root/'artifacts/NS_P14_LEAN_RUN14_PARTIAL_20261110.zip';a.parent.mkdir(exist_ok=True)
with zipfile.ZipFile(a,'w',zipfile.ZIP_DEFLATED) as z:
 for p,b in payload.items():z.writestr(p,b)
 z.writestr('MANIFEST_SHA256.json',json.dumps(manifest,ensure_ascii=False,indent=2)+'\n')
with zipfile.ZipFile(a) as z:
 assert set(z.namelist())==set(payload)|{'MANIFEST_SHA256.json'}
 for p,h in manifest.items():assert hashlib.sha256(z.read(p)).hexdigest()==h
 assert z.testzip() is None
sha=hashlib.sha256(a.read_bytes()).hexdigest();a.with_suffix('.sha256').write_text(sha+'  '+a.name+'\n')
print(json.dumps(dict(status=s['status'],archive=str(a.relative_to(root)),sha256=sha,entries=len(payload)+1),indent=2))
