#!/usr/bin/env python3
"""Read-only independent R03 inventory/DAG probe. Imports no repository code."""
from pathlib import Path
import ast, collections, gzip, hashlib, json, sys
sys.setrecursionlimit(20000)
ROOT = Path('/workspace/NS-P14-Lean-run18')
SRC = ROOT/'verification/run20/sources'
RUN = ROOT/'verification/run20/runs/release_20261116_r03'
def gz(p):
    return json.loads(gzip.decompress(p.read_bytes()))
def digest(v):
    return hashlib.sha256(json.dumps(v, ensure_ascii=False, separators=(',', ':')).encode()).hexdigest()
mods = {'NSP14'} | {str(p.relative_to(ROOT))[:-5].replace('/', '.') for d in ['NSP14','tests','audit'] for p in (ROOT/d).rglob('*.lean')}
rows = gz(RUN/'declarations.json.gz')
base = gz(SRC/'base_declarations.json.gz')
expected = gz(SRC/'expected_declarations.json.gz')
expected2 = gz(SRC/'expected_declarations_hash.json.gz')
meta = json.loads((RUN/'environment_import_coverage.json').read_text())
names = {r['name'] for r in rows}
assert len(rows) == len(names) == len(expected) == len(expected2)
assert names == set(expected) == set(expected2) == set(meta['declaration_inventory'])
assert mods <= set(meta['imported_modules'])
assert {r['module'] for r in rows} <= mods
assert all({'type','explicit_type','kernel_type','kernel_metadata','explicit_metadata','universe_parameters','axioms'} <= r.keys() for r in rows)
assert all(r['kernel_alpha_roundtrip'] is True and r['kernel_dag_roundtrip'] is True for r in rows)
assert all(set(r['axioms']) <= {'propext','Classical.choice','Quot.sound'} and r['name'] not in r['axioms'] for r in rows)
print('modules',len(mods),dict(collections.Counter(m.split('.')[0] for m in mods)),flush=True)
print('rows',len(rows),'module_counts',dict(collections.Counter(r['module'].split('.')[0] for r in rows)), 'private',sum(r['name'].startswith('_private.') for r in rows),'owning_modules',len({r['module'] for r in rows}),'import_only',len(mods-{r['module'] for r in rows}),flush=True)
print('kinds',dict(collections.Counter(r['kind'] for r in rows)),'axioms',dict(collections.Counter(a for r in rows for a in r['axioms'])),flush=True)
for f in ['DeclarationNames.lean','DeclarationNamesHash.lean']:
    imports={l.removeprefix('import all ') for l in (SRC/f).read_text().splitlines() if l.startswith('import all ')}
    assert imports == mods
    objects=[json.loads(l) for l in gzip.decompress((SRC/f.replace('.lean','.log.gz')).read_bytes()).decode().splitlines() if l.startswith('{')]
    frozen=next(x['complete_name_inventory'] for x in objects if 'complete_name_inventory' in x)
    assert len(frozen)==len(rows) and set(frozen)==names
print('two independent stored name inventories and their logs match all rows; both import all modules',flush=True)
helpers=next(ast.literal_eval(n.value) for n in ast.parse((ROOT/'scripts/verify_run19.py').read_text()).body if isinstance(n,ast.Assign) and any(isinstance(t,ast.Name) and t.id=='FIXTURE_HELPERS' for t in n.targets))
required={(m,prefix+'.'+n) for m,(prefix,ns) in helpers.items() for n in ns}
assert required <= {(r['module'],r['name']) for r in rows}
print('fixed named fixture helpers',len(required),'all present',flush=True)
now={r['name']:r for r in rows}
assert {r['name'] for r in base} <= names
public=[r for r in base if not r['name'].startswith('_private.')]
assert all(all(r[k]==now[r['name']][k] for k in ['type','explicit_type','universe_parameters']) for r in public)
assert sorted(base,key=lambda r:r['name'])==sorted(gz(RUN/'base_environment_parts/declarations.json.gz'),key=lambda r:r['name'])
print('base rows',len(base),'public rows',len(public),'all names retained; type/explicit_type/universe_parameters match; stored replay exactly matches golden',flush=True)
selected=[]
codec=(SRC/'kernel_type_codec.inc').read_text().rstrip()
for p in sorted((RUN/'environment_parts').glob('Part*.lean')):
    text=p.read_text(); body=text[text.index('namespace Run20TypeEncoding'):text.index('end Run20TypeEncoding')+len('end Run20TypeEncoding')]
    assert body==codec
    assert {l.removeprefix('import all ') for l in text.splitlines() if l.startswith('import all ')}==mods
    proc=json.loads(p.with_suffix('.process.json').read_text())
    assert proc['passed'] is True and proc['exit_code']==0
    selected+=proc['selected_modules']
assert set(selected)==mods and len(selected)==len(mods)
print('eight saved parts have exact current codec, import all modules, disjoint full selection, recorded exit 0',flush=True)
arity={'bvar':2,'fvar':2,'mvar':2,'sort':2,'const':3,'app':3,'forall':5,'lambda':5,'let':6,'proj':4,'nat':2,'string':2,'metadata':3}
children={'app':(1,2),'forall':(2,3),'lambda':(2,3),'let':(2,3,4),'proj':(3,),'metadata':(2,)}
def check_name(n):
    if n==[]:return
    assert isinstance(n,list) and len(n)==3 and n[1] in ['s','n']
    assert type(n[2]) is (str if n[1]=='s' else int)
    if n[1]=='n': assert n[2]>=0
    check_name(n[0])
def check_level(n):
    assert n[0] in ['zero','succ','max','imax','param','mvar']
    assert len(n)=={'zero':1,'succ':2,'max':3,'imax':3,'param':2,'mvar':2}[n[0]]
    if n[0] in ['param','mvar']:check_name(n[1])
    else:
        for x in n[1:]:check_level(x)
def structural_key(nodes, md, idx, depth, normalize, memo):
    k=(idx,depth if normalize else 0)
    if k in memo:return memo[k]
    a=list(nodes[idx]);tag=a[0]
    for p in children.get(tag,()):
        deeper=(tag in ['forall','lambda'] and p==3) or (tag=='let' and p==4)
        a[p]=structural_key(nodes,md,a[p],depth+int(deeper),normalize,memo)
    if normalize and tag in ['forall','lambda','let']:a[1]=[[],'s','__run20_binder_'+str(depth)]
    if tag=='metadata':a[1]=md[a[1]]
    result=digest(a);memo[k]=result;return result
counts={k:collections.Counter() for k in ['kernel_type','explicit_type']}
mdvalues=collections.Counter();binders=collections.Counter();totals=collections.Counter()
for row in rows:
    dags={k:json.loads(row[k]) for k in counts}
    for field,d in dags.items():
        nodes=d['nodes'];md=row['kernel_metadata' if field=='kernel_type' else 'explicit_metadata']
        assert d['encoding']=='Lean.Expr.DAG.v1' and type(d['root']) is int and 0<=d['root']<len(nodes)
        totals[field]+=len(nodes)
        if field=='kernel_type':mdvalues.update(md);totals['metadata_rows']+=bool(md)
        for i,n in enumerate(nodes):
            tag=n[0];counts[field][tag]+=1;assert len(n)==arity[tag]
            for p in children.get(tag,()):assert type(n[p]) is int and 0<=n[p]<i
            if tag in ['fvar','mvar','const','forall','lambda','let','proj']:check_name(n[1])
            if tag=='sort':check_level(n[1])
            if tag=='const':
                for level in n[2]:check_level(level)
            if tag in ['forall','lambda']:
                assert n[4] in [0,1,2,3]
                if field=='kernel_type':binders[n[4]]+=1
            if tag=='let':assert type(n[5]) is bool
            if tag=='metadata':assert type(n[1]) is int and 0<=n[1]<len(md)
    o=dags['kernel_type'];e=dags['explicit_type']
    assert structural_key(o['nodes'],row['kernel_metadata'],o['root'],0,True,{})==structural_key(e['nodes'],row['explicit_metadata'],e['root'],0,False,{}), row['name']
print('all saved DAG shapes, constructor arities, Name/Level shapes, child<parent references, binder kinds, let flags, metadata references passed',flush=True)
print('all',len(rows),'original-to-canonical structural hashes match (including metadata snapshot strings)',flush=True)
print('node_totals',dict(totals),'constructor_counts',{k:dict(v) for k,v in counts.items()},flush=True)
print('binder_kinds',dict(binders),'metadata_snapshot_values',dict(mdvalues),flush=True)
print('PASS_READ_ONLY_SAVED_R03_INDEPENDENT_PROBE; no Lean/Lake/checker/packager invoked',flush=True)
