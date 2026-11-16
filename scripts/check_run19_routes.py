#!/usr/bin/env python3
"""Root-specific proof route checks, separate from the transitive axiom audit."""
from pathlib import Path
import argparse, hashlib, importlib.util, json, re, subprocess
ROOT=Path(__file__).resolve().parents[1]
spec=importlib.util.spec_from_file_location('v06_routes',ROOT/'scripts/check_v06_routes.py')
v06=importlib.util.module_from_spec(spec);spec.loader.exec_module(v06)
ROUTES=[
('NSP14/NarrowFour/CubicPayment.lean','second_payment',['cubic_gap'],[]),
('NSP14/NarrowFour/HigherRows.lean','actual_higher_envelopes',['actual_two_row_two','actual_two_row_three','actual_two_row_four','distance_volume_four_add'],[]),
('NSP14/NarrowFour/HigherRows.lean','actual_large_higher',['actual_higher_envelopes','second_payment','third_payment','fourth_payment'],[]),
('NSP14/NarrowFour/HigherRows.lean','narrow_four_higher',['actual_large_higher','physical_capacity'],[]),
('NSP14/NarrowFour/WidthFourCompetitors.lean','column_dead_iff',['all_j_threshold','restricted_long_impossible'],['competitorFiber_stopping']),
('NSP14/NarrowFour/WidthFourInitial.lean','candidateLift_injective',['live_images_independent'],[]),
('NSP14/NarrowFour/WidthFourInitial.lean','actual_kernel_eq',['candidateLift_injective'],[]),
('NSP14/NarrowFour/WidthFourComparison.lean','actual_first_le_family',['actual_kernel_eq','first_le_generators'],[]),
('NSP14/NarrowFour/WidthFourComparison.lean','width_four_comparison',['actual_first_bound','generatorBound_payment','target_first'],[]),
('NSP14/NarrowFour/Comparison.lean','narrow_four_comparison',['narrow_four_higher','width_four_comparison','narrow_four_small','narrow_four_first_large'],[]),
('NSP14/SmallEmbedding/LanTuVu.lean','positive_minimal_witness',['exists_minimalFiber_le','forbiddenStart_le','forbiddenStart_height'],['stoppingStart']),
('NSP14/SmallEmbedding/LanTuVu.lean','competitor_sum_refined',['minimalEncoding_injective','competitorMin_card'],[]),
('NSP14/SmallEmbedding/LanTuVu.lean','actualR_one_bound',['actualR_refined','coreCost_degree','minimalDegreeIndex_injective','sum_truncated_degree'],[]),
('NSP14/SmallEmbedding/ThreeComparison.lean','one_actual_profile',['actual_one_rows','one_coreP_bound','actualR_one_bound','one_first_payment','one_second_payment'],[]),
('NSP14/SmallEmbedding/ThreeComparison.lean','three_comparison',['one_actual_profile','three_physical_capacity','three_wide_comparison','three_narrow_fullAP_comparison'],[])]

def check():
    inherited=v06.check();records=[]
    for path,name,required,forbidden in ROUTES:
        text=v06.body(path,name);tokens=set(re.findall(r"[A-Za-z_][A-Za-z_0-9'.]*",text));leaf={t.rsplit('.',1)[-1] for t in tokens}
        if not set(required)<=leaf:raise ValueError((name,'missing direct reference',set(required)-leaf))
        if set(forbidden)&leaf:raise ValueError((name,'forbidden reference'))
        records.append({'path':path,'root':name,'required':required,'forbidden':forbidden,'body_sha256':hashlib.sha256(text.encode()).hexdigest()})
    closures={}
    for m in ['NSP14.NarrowFour.Comparison','NSP14.SmallEmbedding.ThreeComparison']:
        c=v06.closure(m)
        if 'NSP14.Endpoint.Stopping' in c:raise ValueError('Stopping reintroduced: '+m)
        closures[m]=c
    policy=json.loads((ROOT/'docs/RUN19_CHANGE_POLICY.json').read_text())
    root_closure=v06.closure('NSP14')
    if not {p[:-5].replace('/','.') for p in policy['new_production']}<=set(root_closure):raise ValueError('umbrella reachability missing')
    replay=subprocess.run(['python3','verification/run19/sources/replay_three_port.py'],cwd=ROOT,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
    if replay.returncode:raise ValueError('positive-alphabet proof replay differs: '+replay.stdout)
    return {'status':'PASS_RUN19_ROUTES','inherited_v06':inherited,'new_routes':records,'main_import_closures':closures,
      'positive_alphabet_replay':replay.stdout.strip(),'method':'actual source declaration references/import closures; mathematical proof-body review is separately required'}
def main():
    p=argparse.ArgumentParser();p.add_argument('--output',required=True);a=p.parse_args();rel=Path(a.output)
    if rel.is_absolute() or '..' in rel.parts or rel.parts[:3]!=('verification','run19','runs'):p.error('new Run19 output required')
    out=ROOT/rel
    if out.exists() or any(x.is_symlink() for x in [out,*out.parents] if x.is_relative_to(ROOT)):p.error('existing/symlink output forbidden')
    with out.open('x') as f:json.dump(check(),f,indent=2);f.write('\n')
    print('PASS_RUN19_ROUTES',len(ROUTES),'new roots; 13 inherited roots')
if __name__=='__main__':main()
