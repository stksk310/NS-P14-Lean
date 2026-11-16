#!/usr/bin/env python3
"""Independent finite transcription and actual-core regressions; not universal proofs."""
from fractions import Fraction as Q
from itertools import combinations
from math import comb,gcd
from pathlib import Path
import argparse,importlib.util,json
ROOT=Path(__file__).resolve().parents[1]
def choose(n,k):return comb(n,k)if 0<=k<=n else 0
def capacity(e,u,i):return Q(i*choose(u,i+1)+u*choose(e-1,i-1)+choose(e-1,i+1),choose(e,i))
def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--output',required=True);args=p.parse_args()
    rel=Path(args.output)
    if rel.is_absolute()or'..'in rel.parts or rel.parts[:2]!=('verification','run18'):p.error('output must be under verification/run18')
    out=ROOT/rel
    if out.exists():p.error('output already exists')
    identities=payments=ratios=0
    for e in range(6,26):
        a=e-1;s=e//2
        for u in range(2*e-2,2*e+32):
            k,b=divmod(u-a,s);B=u+sum(max(u-a-s*j,0)for j in range(u))
            assert B==u+Q((u-a)**2,2*s)+Q(u-a,2)+Q(b*(s-b),2*s)
            assert 2*a*(Q(u*u,a)-B)==s*(2*s-a)*k*k+a*s*k+2*(2*s-a)*k*b+2*b*b
            identities+=2
            first=Q(e+3,3)*B-u+Q(e*(e-1),6)
            fourth=Q(e+5,4)*B-u+Q((e-1)*e*(e+1),24)
            assert min(first,fourth)<=choose(u,2)+1
            assert B<=capacity(e,u,2)
            for i in range(2,e+1):
                assert capacity(e,u,2)<=capacity(e,u,i)
                assert B*choose(e,i)<=i*choose(u,i+1)+u*choose(e-1,i-1)+choose(e-1,i+1)
                payments+=1
                if i<e:
                    assert Q(choose(u,i),choose(e,i))<=Q(choose(u,i+1),choose(e,i+1))
                    ratios+=1
    for v in range(12):
        for z in range(20):
            e=7+v;u=2*e-2+z
            assert 2*u*u-(3*e+6)*u+6*e-2==2*v*v+5*v*z+12*v+2*z*z+21*z+4
            identities+=1
    spec=importlib.util.spec_from_file_location('run16_coordinates',ROOT/'scripts/check_run16_coordinates.py')
    model=importlib.util.module_from_spec(spec);spec.loader.exec_module(model)
    records=[]
    for m,d,a,u in [(12,1,[1,2,8,9],10),(32,3,[1,2,8,9],10),(14,1,[1,2,3,4,5],12),(16,1,[1,2,3,4,5,6],14),(18,1,[1,2,3,4,5,6,7],16),(20,1,[1,2,3,4,5,6,7,8],18)]:
        r=model.check(m,d,a,u,matrices=len(a)==4)
        assert m>=d*u+2 and gcd(m,d)==1
        assert (len(a)+1)*r['W']<=u*u
        if 'QC_Betti_by_characteristic'in r:
            for characteristic,betti in r['QC_Betti_by_characteristic'].items():
                for i in range(1,len(a)+3):
                    core=betti[i]if i<len(betti)else 0
                    upper=core+r['PC']*choose(len(a),i-1)+r['R']*choose(len(a)+1,i-1)
                    assert upper<=choose(u,2)+1 if i==1 else upper<=i*choose(u,i+1)
        records.append(r)
    assert(records[0]['PC'],records[0]['PG'],records[0]['R'])==(15,10,1)
    result=dict(status='PASS_FINITE_TRANSCRIPTION_AND_CORE_REGRESSIONS_NOT_UNIVERSAL_PROOF',
        arithmetic_identities=identities,row_payments=payments,adjacent_ratios=ratios,
        exact_core_examples=records,characteristics='0, 2, 3 computed separately for four internal variables',
        note='No equality of ranks across characteristics is assumed. Universal closure is the Lean sparse_closed theorem.')
    out.parent.mkdir(parents=True,exist_ok=True)
    with out.open('x')as f:json.dump(result,f,indent=2);f.write('\n')
    print(result['status'],identities,payments,ratios,len(records))
if __name__=='__main__':main()
