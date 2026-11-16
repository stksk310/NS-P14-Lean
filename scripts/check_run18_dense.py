#!/usr/bin/env python3
"""Exact finite dense payment and separately computed QC/lex regressions; Lean proves universality."""
from pathlib import Path
from fractions import Fraction
from math import comb,gcd
from collections import Counter
import argparse,importlib.util,json
ROOT=Path(__file__).resolve().parents[1]
def choose(n,k):return comb(n,k)if 0<=k<=n else 0
def compositions(q,n):
    if q==1:
        yield(n,);return
    for a in range(n+1):
        for b in compositions(q-1,n-a):yield(a,*b)
def lex_model(q,hilbert):
    top=max(hilbert);std={n:set(sorted(compositions(q,n))[:hilbert.get(n,0)])for n in range(top+2)}
    assert all(len(std[n])==hilbert.get(n,0)for n in std)
    generators=[]
    for n in range(1,top+2):
        for a in compositions(q,n):
            if a in std[n]:continue
            parents=[tuple(v-(i==j)for i,v in enumerate(a))for j in range(q)if a[j]]
            if all(b in std[n-1]for b in parents):generators.append(a)
            for j in range(q):
                child=tuple(v+(i==j)for i,v in enumerate(a))
                if n<=top:assert child not in std[n+1]
    maxvar=lambda a:max((i+1 for i,v in enumerate(a)if v),default=0)
    K=sum(q-maxvar(a)for n,row in std.items()if n>=2 for a in row)
    betti=[1]+[sum(choose(maxvar(a)-1,i-1)for a in generators)for i in range(1,q+1)]
    assert betti[1]==choose(q+1,2)+K
    for i in range(1,q+1):assert betti[i]<=i*choose(q+1,i+1)+K*choose(q-1,i-1)
    return dict(Hilbert=dict(sorted(hilbert.items())),K=K,minimal_generators=generators,lex_Betti=betti)
def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--output',required=True);a=p.parse_args();rel=Path(a.output)
    if rel.is_absolute()or'..'in rel.parts or rel.parts[:2]!=('verification','run18'):p.error('output must be under verification/run18')
    out=ROOT/rel
    if out.exists():p.error('output already exists')
    payments=0;boundaries=[]
    for q in range(4,81):
        for t in range(2,q+1):
            P=q+1+2*t;R=0 if t==2 else t;K=2 if t==2 else 4 if t==3 else 2*t*(t-1)//3
            for i in range(1,q+3):
                upper=i*choose(q+1,i+1)+P*choose(q,i-1)+R*choose(q+1,i-1)+K*choose(q-1,i-1)
                target=i*choose(q+t+1,i+1);assert upper<=target;payments+=1
                if q==4 and i in [1,2,6]:boundaries.append(dict(q=q,t=t,i=i,P=P,R=R,K=K,upper=upper,target_first_term=target))
    spec=importlib.util.spec_from_file_location('run16_dense_coordinates',ROOT/'scripts/check_run16_coordinates.py');model=importlib.util.module_from_spec(spec);spec.loader.exec_module(model)
    records=[]
    for m,d,alphabet,u in [(9,1,[1,2,3,4],7),(23,3,[1,2,3,4],7),(10,1,[1,2,3,4],8),(26,3,[1,2,3,4],8),(11,1,[1,2,3,4],9),(29,3,[1,2,3,4],9)]:
        actual=model.check(m,d,alphabet,u,matrices=True);q=len(alphabet);t=u-q-1
        assert m==d*u+2 and gcd(m,d)==1
        offsets=[0,*alphabet,u];sums=[{0}]
        for _ in range(2*u+1):sums.append({x+y for x in offsets for y in sums[-1]})
        inside=lambda r,L,K:r+u*K in sums[L+K+(r!=0)]
        basis=[(L+K+(r!=0),r+u*K)for r in range(u)for L in range(u)for K in range(u)if inside(r,L,K)and(L==0 or not inside(r,L-1,K))and(K==0 or not inside(r,L,K-1))]
        assert len(basis)==actual['PC']
        lex=lex_model(q,Counter(n for n,_ in basis));K=lex['K'];r=3 if t<=3 else t
        assert choose(r+1,2)>=2*t
        assert Fraction(K)<=Fraction(2*t*(r-1),3)
        for characteristic,betti in actual['QC_Betti_by_characteristic'].items():
            for i in range(1,q+3):
                qc=betti[i]if i<len(betti)else 0;lb=lex['lex_Betti'][i]if i<len(lex['lex_Betti'])else 0
                assert qc<=lb
                full_upper=lb+actual['PC']*choose(q,i-1)+actual['R']*choose(q+1,i-1)
                assert full_upper<=i*choose(u,i+1)
        records.append(dict(actual=actual,lex=lex))
    result=dict(status='PASS_FINITE_DENSE_AND_ACTUAL_CORE_REGRESSIONS_NOT_UNIVERSAL_PROOF',row_payments=payments,q_range=[4,80],boundary_rows=boundaries,actual_core_and_lex_examples=records,
        characteristics='0, 2, 3 computed separately; no cross-characteristic rank equality assumed',universal_exports=['NSP14.Width.dense_payment','NSP14.NumericalSemigroup.narrow_dense_comparison','NSP14.NumericalSemigroup.narrow_width_comparison'])
    out.parent.mkdir(parents=True,exist_ok=True)
    with out.open('x')as f:json.dump(result,f,indent=2);f.write('\n')
    print(result['status'],payments,len(records),'actual core/lex cases')
if __name__=='__main__':main()
