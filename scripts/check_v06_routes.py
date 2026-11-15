#!/usr/bin/env python3
"""Check V06 import closures and explicit source-level proof-route obligations.

This checker does not pretend to reconstruct erased imported proof bodies. Its
per-root direct-call checks accompany the independent proof-body review; Lean
collectAxioms is a separate check in verify_v06_alignment.py.
"""
from pathlib import Path
import argparse, hashlib, json, re
ROOT=Path(__file__).resolve().parents[1]

def clean(text):
    # Preserve line positions while removing nested Lean comments and strings.
    out=[]; i=0; depth=0; string=False
    while i<len(text):
        c=text[i]; pair=text[i:i+2]
        if depth:
            if pair=='/-':depth+=1;out.extend('  ');i+=2;continue
            if pair=='-/':depth-=1;out.extend('  ');i+=2;continue
            out.append('\n' if c=='\n' else ' ');i+=1;continue
        if string:
            if c=='\\':out.extend('  ');i+=2;continue
            if c=='"':string=False
            out.append('\n' if c=='\n' else ' ');i+=1;continue
        if pair=='/-':depth=1;out.extend('  ');i+=2;continue
        if pair=='--':
            j=text.find('\n',i)
            if j<0:j=len(text)
            out.extend(' '*(j-i));i=j;continue
        if c=='"':string=True;out.append(' ');i+=1;continue
        out.append(c);i+=1
    assert depth==0 and not string,'unclosed comment/string'
    return ''.join(out)

def imports(module):
    p=ROOT/(module.replace('.','/')+'.lean')
    if not p.is_file():return []
    return re.findall(r'^\s*(?:public\s+)?import\s+([\w.]+)',clean(p.read_text()),re.M)

def closure(module):
    seen=set();active=set()
    def visit(m):
        if m in seen:return
        assert m not in active,('import cycle',m)
        active.add(m)
        for n in imports(m):visit(n)
        active.remove(m);seen.add(m)
    visit(module)
    return sorted(seen)

def body(path,name):
    s=clean((ROOT/path).read_text())
    found=list(re.finditer(r'^(?:private\s+|protected\s+)?(?:noncomputable\s+)?(?:theorem|lemma|def|abbrev)\s+'+re.escape(name)+r'(?=\s|\()',s,re.M))
    assert len(found)==1,('declaration coverage',path,name)
    tail=s[found[0].start():]
    stop=re.search(r'\n(?:end\b|namespace\b|(?:private\s+|protected\s+)?(?:noncomputable\s+)?(?:theorem|lemma|def|abbrev)\s+)',tail)
    return tail[:stop.start()] if stop else tail

# Every entry is a named proof root, not an import-level ban on retained APIs.
ROUTES=[
('NSP14/Endpoint/CompetitorBounds.lean','competitorMin_height',
 ['exists_minimalFiber_le','forbiddenStart_le','eq_of_le','minimalPoint_height','forbiddenStart_height'],
 ['competitorFiber_stopping','forbiddenStart_mono','stoppingStart']),
('NSP14/Endpoint/FiniteSocleBounds.lean','competitor_zero_column',
 ['forbiddenStart_height','coreHeight_le','carry_u','minimalFiber_budget'],
 ['forbiddenStart_tail_zero','stoppingStart','competitorFiber_stopping']),
('NSP14/Width/AntipodalComparison.lean','actual_antipodal_first',
 ['antipodal_integer_payment','antipodal_coreP_bound','QCore_first_third','actual_core_endpoint_bound'],
 ['five_wordVolume_eight','antipodal_coreP','antipodal_wordVolume','antipodal_actual_betti','antipodalPresentation','by_cases']),
('NSP14/Width/FiveNonAntipodal.lean','actual_five_nonAntipodal_first',
 ['nonAntipodal_integer_payment','five_nonAntipodal_volume_remainder','actual_first_volume_fourth'],
 ['interval_cases','by_cases','growthVolume_remainder_identity','growthVolume']),
('NSP14/Width/HigherFromSecond.lean','higher_capacity_from_second',
 ['normalized_capacity_monotone','choose_pos'], ['actual_five_higher','actual_sparse_higher','comparison']),
('NSP14/Width/HigherFromSecond.lean','actual_resource_envelope_add',
 ['actual_positive_rows_add','choose_succ_succ'], ['actual_five_higher','actual_sparse_higher','comparison']),
('NSP14/Width/HigherFromSecond.lean','actual_higher_from_second',
 ['higher_capacity_from_second','actual_resource_envelope_add'], ['actual_five_higher','actual_sparse_higher','comparison']),
('NSP14/Width/FiveHigher.lean','actual_five_higher',
 ['actual_higher_from_second','five_wordVolume_eight','actual_endpoint_above'], ['choose_quadratic_step','choose_quadratic_from_eight']),
('NSP14/Width/SparseHigher.lean','actual_sparse_higher',
 ['actual_higher_from_second','sparse_second_payment'], ['actual_five_higher']),
('NSP14/Width/DenseLexResources.lean','dense_core_lex_bound_two_branch',
 ['exists_core_lex','dense_lex_correction_bound'], ['dense_core_lex_bound']),
('NSP14/Width/DensePayment.lean','dense_coeff_ge_three',
 ['dense_gamma_nonneg'], ['dense_large_coeff','dense_payment']),
('NSP14/Width/DensePayment.lean','dense_payment_ge_three',
 ['dense_coeff_ge_three','choose_add_two_terms'], ['dense_payment','dense_large_coeff']),
('NSP14/Width/DenseComparison.lean','actual_dense_firstterm',
 ['dense_core_lex_bound_two_branch','dense_payment_two','dense_payment_ge_three','actual_core_endpoint_bound'],
 ['dense_core_lex_bound','dense_payment','dense_large_coeff'])]

def check():
    records=[]
    for path,name,required,forbidden in ROUTES:
        text=body(path,name)
        tokens=set(re.findall(r"[A-Za-z_][A-Za-z_0-9'.]*",text))
        leaf={t.rsplit('.',1)[-1] for t in tokens}
        assert set(required)<=leaf,(name,'missing route',set(required)-leaf)
        assert not set(forbidden)&leaf,(name,'forbidden route',set(forbidden)&leaf)
        records.append(dict(source=path,root=name,required_direct_references=required,
          forbidden_direct_references=forbidden,source_sha256=hashlib.sha256((ROOT/path).read_bytes()).hexdigest(),
          declaration_sha256=hashlib.sha256(text.encode()).hexdigest()))
    closures={}
    for module in ['NSP14.Endpoint.RowPackage','NSP14.Endpoint.SocleBounds','NSP14.Width.Closure']:
        c=closure(module)
        assert 'NSP14.Endpoint.Stopping' not in c,module
        closures[module]=c
    finite=closure('NSP14.Endpoint.FiniteCompetitors')
    assert 'NSP14.Endpoint.Stopping' in finite
    for module in ['NSP14.Width.IntegerPayment','NSP14.Width.HigherFromSecond']:
        assert module in closure('NSP14'),('umbrella reachability',module)
    low=closure('NSP14.Width.HigherFromSecond')
    assert not {'NSP14.Width.SparseHigher','NSP14.Width.FiveHigher','NSP14.Width.Closure'}&set(low)
    return dict(status='PASS_V06_SOURCE_ROUTES',method='individual import closure + direct declaration reference checks; independent proof-body review required for transitive mathematics',
      routes=records,main_import_closures=closures,finite_computational_closure=finite,
      higher_wrapper_closure=low,main_stopping_absent=True,old_finite_stopping_retained=True)

def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--output',required=True);a=p.parse_args()
    rel=Path(a.output)
    if rel.is_absolute() or '..' in rel.parts or rel.parts[:3]!=('verification','run18','runs') or len(rel.parts)<5 or not rel.parts[3].startswith('v06_alignment_'):p.error('unique V06 run output required')
    dest=ROOT/rel
    if not dest.resolve().is_relative_to(ROOT.resolve()):p.error('output escapes repository')
    if any(part.is_symlink() for part in [dest,*dest.parents] if part.is_relative_to(ROOT)):
        p.error('symlink output path is forbidden')
    if dest.exists():p.error('output already exists')
    result=check()
    with dest.open('x') as f:f.write(json.dumps(result,ensure_ascii=False,indent=2)+'\n')
    print(result['status'],len(result['routes']),'named roots')
if __name__=='__main__':main()
