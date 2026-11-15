#!/usr/bin/env python3
"""Independent exact arithmetic and actual graded Koszul regressions.

Finite checks are never an input to a universal Lean theorem. Characteristic ranks
are computed separately; equality across characteristics is not assumed.
"""
from pathlib import Path
from fractions import Fraction as F
from itertools import combinations
from math import comb, gcd
import argparse, importlib.util, json
ROOT=Path(__file__).resolve().parents[1]
spec=importlib.util.spec_from_file_location('coordinates',ROOT/'scripts/check_run16_coordinates.py')
model=importlib.util.module_from_spec(spec);spec.loader.exec_module(model)

def C(n,k):return comb(n,k) if 0<=k<=n else 0
def add(a,b):return [(a[i] if i<len(a) else 0)+(b[i] if i<len(b) else 0) for i in range(max(len(a),len(b)))]
def scale(a,c):return [c*x for x in a]
def mul(a,b):
    c=[F(0)]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b):c[i+j]+=x*y
    return c

def actual_g(gens,degree_max):
    """Degree components from maximal decomposition lengths, not core coordinates."""
    bound=(degree_max+1)*max(gens)
    order=[-1]*(bound+1);order[0]=0
    for n in range(1,bound+1):
        for g in gens:
            if n>=g and order[n-g]>=0:order[n]=max(order[n],order[n-g]+1)
    bases={t:[n for n,o in enumerate(order) if o==t] for t in range(degree_max+1)}
    rows=[];e=len(gens)
    for t in range(degree_max+1):
        chain={i:[(I,n) for I in combinations(range(e),i) for n in bases.get(t-i,[])] for i in range(e+1)}
        ranks={p:[0]*(e+2) for p in [0,2,3]}
        for i in range(1,e+1):
            dest={x:j for j,x in enumerate(chain[i-1])}
            mat=[[0]*len(chain[i]) for _ in chain[i-1]]
            for j,(I,n) in enumerate(chain[i]):
                for a,v in enumerate(I):
                    if order[n+gens[v]]==t-i+1:
                        r=dest[(I[:a]+I[a+1:],n+gens[v])];mat[r][j]+=(-1)**a
            for p in ranks:ranks[p][i]=model.rank(mat,p)
        beta={p:[len(chain[i])-ranks[p][i]-ranks[p][i+1] for i in range(e+1)] for p in ranks}
        assert all(v>=0 for b in beta.values() for v in b)
        rows.append({'degree':t,'chain_dimensions':[len(chain[i]) for i in range(e+1)],'ranks':ranks,'betti':beta})
    return {'generators':gens,'degrees_through':degree_max,'graded_rows':rows,'not_claimed':'no infinite-degree vanishing is inferred from this finite computation'}

def check():
    z=[F(6),F(1)]
    choose3=scale(mul(mul(z,add(z,[-1])),add(z,[-2])),F(1,6))
    U2=add(add(scale(mul(z,z),F(5,4)),scale(z,-2)),[4])
    cubic=scale(add(scale(choose3,2),scale(U2,-1)),12)
    assert cubic==[36,140,45,4]
    arithmetic=0
    for u in range(3,41):
        T=lambda i:i*C(u,i+1)
        U2=F(5*u*u,4)-2*u+4;U3=u*u-3*u+4;U4=F(u*u,4)-u+1
        if u>=6:assert U2<T(2) and U3<=T(3) and U4<=T(4)
        assert 8*T(3)==3*(u-3)*T(2) and 10*T(4)==(u-3)*(u-4)*T(2)
        assert u+C(u-3,2)<=C(u,2) and C(u-3,2)<=C(u,3)
        for b in range(2,u):
            for a in range(1,b):
                h=u//2;k=u-b+a;removed=C(h-k+2,2) if k<=h else 0
                rectangle=sum(1 for s in range(1,h) for t in range(1,h) if s+t<=h and u-b<=s and a<=t)
                assert rectangle==removed
                arithmetic+=1
    theta=[]
    for m in range(6,301):
        values=[max(0,(m-n+3)//4) for n in [0,1,2,3,6]]
        q,r=divmod(m,4)
        expected=[[q,q,q,q,q-1],[q+1,q,q,q,q-1],[q+1,q+1,q,q,q-1],[q+1,q+1,q+1,q,q]][r]
        assert values==expected
        cap=6 if m==6 or r in [0,3] else 8
        assert cap<=10-(m-1)%4
        theta.append({'m':m,'theta':values,'source_bound':cap,'target_first':10-(m-1)%4})
    cores=[]
    for u in range(3,10):
        for a in range(1,u):
            if gcd(a,u)!=1:continue
            for m in range(u+2,u+5):
                for d in [1,2,3]:
                    if gcd(m,d)!=1:continue
                    r=model.check(m,d,[a],u,True)
                    assert r['PC']<=u and r['R']<=C(u-3,2)
                    cores.append(r)
    n4=[model.check(m,d,a,u,True) for m,d,a,u in [(6,1,[1,3],4),(8,1,[1,5],6),(20,3,[2,3],6),(11,1,[2,3],6)]]
    assert (n4[1]['PC'],n4[1]['PG'],n4[1]['R'])==(9,6,1)
    actual=[actual_g(g,7) for g in [[6,7,9,10],[8,9,13,14],[8,9,14],[5,6,8],[3,4,5]]]
    return {'status':'PASS_RUN19_EXACT_REGRESSIONS_NOT_UNIVERSAL_PROOF','cubic_coefficients':[int(x) for x in cubic],
      'arithmetic_cases':arithmetic,'width_four':theta,'one_letter_actual_cores':cores,'n4_actual_cores':n4,
      'actual_graded_G_koszul':actual,'characteristics_independently_computed':[0,2,3]}

def main():
    p=argparse.ArgumentParser();p.add_argument('--output',required=True);a=p.parse_args();rel=Path(a.output)
    if rel.is_absolute() or '..' in rel.parts or rel.parts[:3]!=('verification','run19','runs'):p.error('exclusive Run19 path required')
    out=ROOT/rel
    if out.exists() or any(x.is_symlink() for x in [out,*out.parents] if x.is_relative_to(ROOT)):p.error('existing/symlink output forbidden')
    result=check()
    with out.open('x') as f:json.dump(result,f,indent=2);f.write('\n')
    print(result['status'],result['arithmetic_cases'],'arithmetic cases',len(result['one_letter_actual_cores']),'one-letter cores')
if __name__=='__main__':main()
