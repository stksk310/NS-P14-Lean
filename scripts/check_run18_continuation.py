#!/usr/bin/env python3
"""Exact finite checks of continuation formulas and actual cores; not universal proof."""
from fractions import Fraction as Q
from itertools import combinations
from math import comb,gcd
from pathlib import Path
import argparse,importlib.util,json
ROOT=Path(__file__).resolve().parents[1]
def C(n,k): return comb(n,k) if 0<=k<=n else 0
def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--output',required=True);a=p.parse_args()
    rel=Path(a.output)
    if rel.is_absolute() or '..' in rel.parts or rel.parts[:3]!=('verification','run18','runs'): p.error('new output under verification/run18/runs required')
    out=ROOT/rel
    if out.exists():p.error('existing evidence is immutable')
    arithmetic=0
    for u in range(8,121):
        B=u+sum(max(u-4-3*j,0)for j in range(u))
        assert 6*B<=u*u+u+6
        assert (5*B//2)-u+5<=C(u,2)+1
        for k in range(2,9):
            assert u*u*C(8,k)<=64*C(u,k)
            assert (u+1)**2*C(u,k)<=u*u*C(u+1,k)
            arithmetic+=2
        W=14 if u==8 else Q(u*u,4)
        caps=[10*W-4*u-4,10*W-6*u-1,5*W-4*u,W-u]
        for i,cap in zip(range(2,6),caps):assert cap<=i*C(u,i+1);arithmetic+=1
    for v in range(4,31):
        for c in range(1,v+1):
            for i in range(1,v+4):
                correction=(c+1-i)*C(v,i-1)if i<=c else(i-c)*C(v,i)
                assert i*C(v,i+1)+correction<=i*C(v+1,i+1)
                arithmetic+=1
    spec=importlib.util.spec_from_file_location('coordinates',ROOT/'scripts/check_run16_coordinates.py')
    model=importlib.util.module_from_spec(spec);spec.loader.exec_module(model)
    records=[];positive_R=0
    for u in [6,7]:
        for offsets in combinations(range(1,u),3):
            r=model.check(u+2,1,list(offsets),u,matrices=True)
            t=u-4
            assert r['W']==4+2*t and r['PC']<=4+2*t and r['Hx']<=t and r['R']<=t
            if t<=2:assert r['R']==0
            positive_R+=r['R']>0
            for characteristic,b in r['QC_Betti_by_characteristic'].items():
                assert b[1]<=8 if u==6 else b[1]<=10
                if u==7 and r['R']>0:assert b[1]<=9
                for i in range(1,6):
                    source_cap=(b[i]if i<len(b)else 0)+r['PC']*C(3,i-1)+r['R']*C(4,i-1)
                    assert source_cap<=i*C(u,i+1)+min(C(u,i-1),C(u,i))
            records.append(r)
    for m,d,offsets,u in [(11,1,[1,2,7,8],9),(20,3,[1,2,3],6),(32,3,[2,5,7],10),(10,1,[1,2,3],8),(11,1,[1,2,3],9)]:
        r=model.check(m,d,offsets,u,matrices=True)
        q=len(offsets);t=u-q-1
        if t<=q:
            assert r['W']==q+1+2*t and r['PC']<=r['W'] and r['Hx']<=t and r['R']<=t
        if q==3 and u>=8:
            for b in r['QC_Betti_by_characteristic'].values():
                for i in range(2,6):
                    source_cap=(b[i]if i<len(b)else 0)+r['PC']*C(3,i-1)+r['R']*C(4,i-1)
                    assert source_cap<=i*C(u,i+1)
        records.append(r)
    assert positive_R>0,'conditional R>0 branch must be exercised'
    result=dict(status='PASS_FINITE_CONTINUATION_CHECKS_NOT_UNIVERSAL_PROOF',arithmetic_checks=arithmetic,
        actual_core_examples=records,small_width_R_positive_examples=positive_R,
        note='Characteristics 0/2/3 computed separately. No equality of ranks across characteristics is assumed. The later five-closure checker covers the antipodal branch; general BHP/EK remains open.')
    out.parent.mkdir(parents=True,exist_ok=True)
    with out.open('x')as f:json.dump(result,f,indent=2);f.write('\n')
    print(result['status'],arithmetic,len(records),positive_R)
if __name__=='__main__':main()
