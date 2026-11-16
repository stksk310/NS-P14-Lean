#!/usr/bin/env python3
"""Parallelize serialization only; every part imports all every project module.

Each constant receives actual collectAxioms, normal Meta.ppExpr, and a complete
explicit kernel term with checked alpha-equivalent binder normalization.
The public Main also retains standard fully explicit pretty output.
No declaration, body, private view, or mathematical check is sampled or omitted.
"""
from pathlib import Path
from concurrent.futures import ThreadPoolExecutor
import argparse,gzip,hashlib,importlib.util,json,os,subprocess,time
ROOT=Path(__file__).resolve().parents[3]
s=importlib.util.spec_from_file_location('run20_part_verify',ROOT/'scripts/verify_run20.py');v=importlib.util.module_from_spec(s);s.loader.exec_module(v)

def validate_parts(parts,modules):
    typed=set();names=set();combined=[];imports=None
    for part in parts:
        selected=set(part['selected_modules']);rows=part['rows'];meta=part['metadata']
        if typed&selected:raise ValueError('duplicate part module coverage')
        typed|=selected;v.v06.validate_import_coverage(meta,modules)
        v.v06.validate_audit(rows,{r['module'] for r in rows},expected_names=set(meta['declaration_inventory']))
        if any(r['module'] not in selected or not {'type','explicit_type','axioms'}<=r.keys() for r in rows):raise ValueError('part declaration scope/type mismatch')
        now={r['name'] for r in rows}
        if names&now:raise ValueError('duplicate part declaration coverage')
        names|=now;combined+=rows
        current=set(meta['imported_modules'])
        if imports is not None and current!=imports:raise ValueError('part imported environment differs')
        imports=current
    if typed!=set(modules):raise ValueError('part module coverage missing')
    meta={'audit_metadata':True,'imported_modules':sorted(imports or []),'declaration_inventory':sorted(names)}
    return sorted(combined,key=lambda r:r['name']),meta

def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--output-dir',required=True);p.add_argument('--source-root');p.add_argument('--parts',type=int,default=4);p.add_argument('--workers',type=int,default=3);a=p.parse_args()
    out=v.safe(ROOT,a.output_dir)
    if out.exists() or Path(a.output_dir).parts[:3]!=('verification','run20','runs'):p.error('new Run20 audit output required')
    if not 1<=a.workers<=a.parts<=8:p.error('one to eight parts, bounded workers required')
    root=Path(a.source_root).resolve() if a.source_root else ROOT
    modules=v.project_modules(root);ordered=sorted(modules);selections=[ordered[i::a.parts] for i in range(a.parts)]
    out.mkdir(parents=True,exist_ok=False)
    sources={m.replace('.','/')+'.lean':v.sha((root/(m.replace('.','/')+'.lean')).read_bytes()) for m in modules}
    snapshot={'source_root':str(root),'source_commit':v.git(root,'rev-parse','HEAD').decode().strip(),'source_sha256':sources,
      'modules':ordered,'parts':a.parts,'workers':a.workers,'direct_import_all_for_every_module_in_every_part':True}
    v.write_json(out/'snapshot.json',snapshot)
    def worker(pair):
        index,selection=pair;source=out/('Part'+str(index).zfill(2)+'.lean')
        code=v.audit_source(modules,selection)
        code=code.replace(' for (n,ci) in env.constants.toList do',
          ' let started ← IO.monoMsNow\n let mut completedCount : Nat := 0\n for (n,ci) in env.constants.toList do',1)
        progress=json.dumps(str(out/(source.stem+'.progress.json')))
        code=code.replace('   IO.println ((Json.mkObj fields).compress)',
          '   IO.println ((Json.mkObj fields).compress)\n   completedCount := completedCount+1\n   if completedCount%100==0 then\n'+
          '    let elapsed ← IO.monoMsNow\n    IO.FS.writeFile '+progress+' ((Json.mkObj [("completed_declarations",toJson completedCount),("last_name",toJson n.toString),("elapsed_ms",toJson (elapsed-started))]).compress)',1)
        source.write_text(code)
        command=['lake','env','lean','-j1','-M12288',str(source)];start=time.monotonic()
        q=subprocess.run(command,cwd=root,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
        (out/(source.stem+'.log.gz')).write_bytes(gzip.compress(q.stdout.encode(),mtime=0))
        record={'command':command,'cwd':str(root),'exit_code':q.returncode,'seconds':round(time.monotonic()-start,3),'selected_modules':selection,'passed':q.returncode==0 and 'warning:' not in q.stdout}
        v.write_json(out/(source.stem+'.process.json'),record)
        print(source.stem,record['exit_code'],'PASS' if record['passed'] else 'FAIL',flush=True)
        if not record['passed']:raise ValueError('audit part failed: '+source.stem)
        rows,meta=v.parse_audit(q.stdout)
        return {'selected_modules':selection,'rows':rows,'metadata':meta}
    with ThreadPoolExecutor(max_workers=a.workers) as pool:parts=list(pool.map(worker,enumerate(selections)))
    rows,meta=validate_parts(parts,modules)
    if any(v.sha((root/n).read_bytes())!=digest for n,digest in sources.items()):raise ValueError('audit source changed during parts')
    (out/'declarations.json.gz').write_bytes(gzip.compress(json.dumps(rows,ensure_ascii=False).encode(),mtime=0))
    v.write_json(out/'metadata.json',meta)
    v.write_json(out/'complete.json',{'status':'PASS_ALL_AUDIT_PARTS','declarations':len(rows),'modules':len(modules),'collectAxioms_each_declaration':True,'normal_explicit_each_declaration':True})
    print('PASS_ALL_AUDIT_PARTS',len(rows),len(modules),flush=True)
if __name__=='__main__':main()
