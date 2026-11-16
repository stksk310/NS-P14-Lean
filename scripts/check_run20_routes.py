#!/usr/bin/env python3
"""Root-specific production route obligations; separate from axiom checking."""
from pathlib import Path
import argparse,hashlib,importlib.util,json,re
ROOT=Path(__file__).resolve().parents[1]
s=importlib.util.spec_from_file_location('run20_routes_old',ROOT/'scripts/check_run19_routes.py');old=importlib.util.module_from_spec(s);s.loader.exec_module(old)
ROUTES=[
 ('NSP14/Main.lean','p14_totalBetti_le_intervalCompletion',['parameter_partition','intervalComparison_base','intervalComparison_three','intervalComparison_ordinary','intervalComparison_narrow_four','intervalComparison_narrow_many']),
 ('NSP14/Main/Branches.lean','intervalComparison_base',['base_comparison']),
 ('NSP14/Main/Branches.lean','intervalComparison_three',['intervalCompletionAll_completed_totalBetti','three_comparison']),
 ('NSP14/Main/Branches.lean','intervalComparison_ordinary',['intervalCompletionAll_completed_totalBetti','ordinary_actual_completion_betti_le']),
 ('NSP14/Main/Branches.lean','intervalComparison_narrow_four',['intervalCompletionAll_completed_totalBetti','narrow_four_comparison']),
 ('NSP14/Main/Branches.lean','intervalComparison_narrow_many',['intervalCompletionAll_completed_totalBetti','narrow_width_comparison']),
 ('NSP14/Main/IntervalTarget.lean','carrier_completed_totalBetti',['completed_totalBetti','carrier_totalBetti']),
 ('NSP14/Main/Partition.lean','cut_parameters',['actualCutRank_two_le','actualCutRank_le','actualCutRank_triangular','degree_two_le_deficit']),
 ('NSP14/Main/Partition.lean','narrow_parameters',['endpointData_embedding','endpointData_narrow','endpointData_generators','endpointData_carrier','width_factor']),
 ('NSP14/Ordinary/NumericalBettiClosure.lean','ordinary_betti_bound',['actualG_totalBetti_baseChange','ordinary_betti_bound_extension']),
]
def check():
    inherited=old.check();records=[]
    for path,name,required in ROUTES:
        text=old.v06.body(path,name);tokens={s.rsplit('.',1)[-1] for s in re.findall(r"[A-Za-z_][A-Za-z_0-9'.]*",text)}
        if not set(required)<=tokens:raise ValueError('missing Main route: '+name+' '+repr(set(required)-tokens))
        records.append({'path':path,'root':name,'required':required,'body_sha256':hashlib.sha256(text.encode()).hexdigest()})
    closure=old.v06.closure('NSP14.Main')
    forbidden={m for m in closure if m.startswith(('audit.','tests.')) or m=='NSP14.Endpoint.Stopping'}
    if forbidden:raise ValueError('nonproduction/legacy main import: '+repr(forbidden))
    if any('import '+m not in (ROOT/'tests/MainPublicAPI.lean').read_text() for m in ['NSP14.Main','Mathlib.Algebra.Field.ZMod']):raise ValueError('minimal API fixture differs')
    return {'status':'PASS_RUN20_MAIN_ROUTES','new_roots':records,'inherited':inherited,'production_main_import_closure':closure,
      'no_test_audit_or_stopping_in_main':True,'method':'named source proof-body references and import closures, plus separate independent mathematical review; erased imported proof bodies are not reconstructed'}
def main():
    p=argparse.ArgumentParser();p.add_argument('--output',required=True);a=p.parse_args()
    from verify_run20 import safe
    out=safe(ROOT,a.output)
    if out.exists() or Path(a.output).parts[:3]!=('verification','run20','runs'):p.error('new Run20 output required')
    result=check()
    with out.open('x') as f:json.dump(result,f,indent=2);f.write('\n')
    print(result['status'],len(ROUTES),'new roots; inherited V06 and Run19 roots retained')
if __name__=='__main__':main()
