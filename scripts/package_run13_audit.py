#!/usr/bin/env python3
"""Package only verified Run13 evidence; never embeds old archives or execution caches."""
from pathlib import Path
import hashlib,json,subprocess,zipfile
root=Path(__file__).resolve().parents[1]
verification=json.loads((root/'verification/block13_continuation/verification.json').read_text())
closure=json.loads((root/'docs/RUN13_CLOSURE_STATUS.json').read_text())
assert verification['status']=='PASS_FORMAL_VERIFICATION'
assert closure['run13_complete'] is True, 'Do not publish an incomplete archive as COMPLETE'
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
archive=root/'artifacts/NS_P14_LEAN_RUN13_COMPLETE_20261110.zip'
archive.parent.mkdir(exist_ok=True)
with zipfile.ZipFile(archive,'w',zipfile.ZIP_DEFLATED) as z:
    for p,b in payload.items():z.writestr(p,b)
    z.writestr('MANIFEST_SHA256.json',json.dumps(manifest,ensure_ascii=False,indent=2)+'\n')
with zipfile.ZipFile(archive) as z:
    assert set(z.namelist())==set(payload)|{'MANIFEST_SHA256.json'}
    for p,h in manifest.items():assert hashlib.sha256(z.read(p)).hexdigest()==h
    assert z.testzip() is None
sha=hashlib.sha256(archive.read_bytes()).hexdigest()
archive.with_suffix('.sha256').write_text(sha+'  '+archive.name+'\n')
print(json.dumps(dict(archive=str(archive.relative_to(root)),sha256=sha,entries=len(payload)+1,manifest_entries=len(payload)),indent=2))
