#!/usr/bin/env python3
"""Finite independent one-hole checks. Universal closure is proved by Lean, not this enumeration."""
import argparse,importlib.util,json
from math import comb
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
def C(n,k):return comb(n,k)if 0<=k<=n else 0
def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--output',required=True);a=p.parse_args();rel=Path(a.output)
    if rel.is_absolute()or'..'in rel.parts or rel.parts[:3]!=('verification','run18','runs'):p.error('new output under verification/run18/runs required')
    out=ROOT/rel
    if out.exists():p.error('existing evidence is immutable')
    spec=importlib.util.spec_from_file_location('coordinates',ROOT/'scripts/check_run16_coordinates.py');model=importlib.util.module_from_spec(spec);spec.loader.exec_module(model)
    records=[]
    for u in range(5,9):
        q=u-2
        for h in range(1,u):
            offsets=[x for x in range(1,u)if x!=h]
            r=model.check(3*u+2,3,offsets,u,matrices=True)
            left=h-1;right=u-h-1
            assert left+right==q and r['PC']==q+(2 if left==0 or right==0 else 3)
            assert r['R']==0 and r['Hx']<=1
            def bad(r,s,j):return C(s,j-r)if r<=j else 0
            def rho(j):return 2*C(q,j)-bad(left,right,j)-bad(right,left,j)
            for ch,b in r['QC_Betti_by_characteristic'].items():
                for i in range(1,q+1):
                    exact=r['PC']*C(q,i)-C(q,i)-C(q,i+1)-rho(i-1)-rho(i)
                    assert b[i]==exact,(u,h,ch,i,b[i],exact)
                for i in range(1,q+4):
                    source_cap=(b[i]if i<len(b)else 0)+r['PC']*C(q,i-1)
                    assert source_cap<=i*C(u,i+1)+min(C(u,i-1),C(u,i))
            records.append(r)
    arithmetic=0
    for q in range(3,31):
        for left in range(1,q):
            right=q-left
            for i in range(1,q+4):
                correction=C(right+1,i-left)+C(left+1,i-right)
                assert correction<=min(C(q+2,i-1),C(q+2,i))
                arithmetic+=1
    result=dict(status='PASS_FINITE_ONE_HOLE_CHECKS_NOT_UNIVERSAL_PROOF',actual_core_examples=records,arithmetic_checks=arithmetic,
        universal_contract='NSP14.Run18.edge_closed : Requested.W_EDGE',
        note='Characteristics 0/2/3 computed independently. Exact rank formulas are finite cross-checks; the universal Lean proof uses actual signed-unit minor lower bounds. BHP/EK and dense/global closure are not certified here.')
    out.parent.mkdir(parents=True,exist_ok=True)
    with out.open('x')as f:json.dump(result,f,indent=2);f.write('\n')
    print(result['status'],len(records),'actual cores',arithmetic,'arithmetic checks')
if __name__=='__main__':main()
