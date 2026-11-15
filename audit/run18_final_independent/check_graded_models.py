#!/usr/bin/env python3
"""Independent finite actual graded quotient/Koszul comparisons; no project imports.

Homogeneous ideal pieces are row spans of all monomial multiples of the given
polynomials. Actual quotient actions use exact RREF reduction. The lex pieces
are built separately from each field's computed Hilbert function.
This is finite evidence, not a universal proof.
"""
from fractions import Fraction as Q
from itertools import combinations
from pathlib import Path
import argparse,json

ap=argparse.ArgumentParser(description=__doc__)
ap.add_argument('--output')
args=ap.parse_args();out=Path(args.output)if args.output else None
if out is not None and out.exists():ap.error('existing evidence is immutable')

def monomials(q,n):
    if n<0:return []
    if q==0:return [()]if n==0 else []
    return [(i,*tail)for i in range(n+1)for tail in monomials(q-1,n-i)]
def add(a,b):return tuple(x+y for x,y in zip(a,b))
def normalize(a,p):return a%p if p else Q(a)
def rref(rows,width,p):
    a=[[normalize(x,p)for x in row]for row in rows];piv=[];r=0
    for col in range(width):
        z=next((z for z in range(r,len(a))if a[z][col]),None)
        if z is None:continue
        a[r],a[z]=a[z],a[r];inv=pow(a[r][col],-1,p)if p else 1/a[r][col]
        a[r]=[normalize(x*inv,p)for x in a[r]]
        for k in range(len(a)):
            if k==r or not a[k][col]:continue
            f=a[k][col];a[k]=[normalize(x-f*y,p)for x,y in zip(a[k],a[r])]
        piv.append(col);r+=1
        if r==len(a):break
    return a[:r],piv
def matrix_rank(a,width,p):return len(rref(a,width,p)[1])

def quotient(q,gens,p,N):
    data=[]
    for n in range(N+1):
        mons=monomials(q,n);ix={a:i for i,a in enumerate(mons)};rels=[]
        for g in gens:
            degree=sum(next(iter(g)))
            assert all(sum(a)==degree for a in g)
            for b in monomials(q,n-degree):
                row=[0]*len(mons)
                for a,c in g.items():row[ix[add(a,b)]]+=c
                rels.append(row)
        rr,piv=rref(rels,len(mons),p);free=[i for i in range(len(mons))if i not in piv]
        data.append(dict(mons=mons,ix=ix,rows=rr,piv=piv,free=free,std=[mons[i]for i in free]))
    def reduce(n,a):
        d=data[n];v=[normalize(int(b==a),p)for b in d['mons']]
        for row,pivot in zip(d['rows'],d['piv']):
            f=v[pivot]
            if f:v=[normalize(x-f*y,p)for x,y in zip(v,row)]
        return [v[i]for i in d['free']]
    return data,reduce

def lex_quotient(q,hilbert,N):
    data=[]
    for n in range(N+1):
        mons=monomials(q,n);std=mons[:hilbert[n]]
        data.append(dict(std=std,mons=mons))
    for n in range(N):
        ideal=set(data[n]['mons'])-set(data[n]['std'])
        for a in ideal:
            for x in range(q):
                child=tuple(v+(i==x)for i,v in enumerate(a))
                assert child not in data[n+1]['std']
    def reduce(n,a):return [int(b==a)for b in data[n]['std']]
    return data,reduce

def graded_betti(q,data,reduce,p,j):
    slots={i:list(combinations(range(q),i))for i in range(q+2)}
    def basis(i):return [(a,J)for a in data[j-i]['std']for J in slots[i]]if 0<=j-i<len(data)else []
    ranks=[0]*(q+3)
    for i in range(1,q+2):
        src=basis(i);dst=basis(i-1);index={x:k for k,x in enumerate(dst)}
        mat=[[0]*len(src)for _ in dst]
        if src and dst:
            n=j-i+1
            for col,(a,J)in enumerate(src):
                for pos,x in enumerate(J):
                    child=tuple(v+(k==x)for k,v in enumerate(a));coeff=reduce(n,child)
                    wedge=J[:pos]+J[pos+1:]
                    for b,c in zip(data[n]['std'],coeff):
                        mat[index[(b,wedge)]][col]+=(-1)**pos*c
        ranks[i]=matrix_rank(mat,len(src),p)
    return [len(basis(i))-ranks[i]-ranks[i+1]for i in range(q+2)]

cases=[
 ('zero_variables',0,[]),('unit_zero_variables',0,[{():1}]),
 ('one_variable',1,[{(1,):1}]),('polynomial',2,[]),
 ('principal_nonArtin',2,[{(2,0):1,(0,2):1}]),
 ('nonlex_CI_two',2,[{(2,0):1,(0,2):1},{(1,1):1}]),
 ('nonlex_CI_three',3,[{(2,0,0):1,(0,2,0):1},{(1,1,0):1},{(0,0,2):1}]),
 ('characteristic_sensitive',2,[{(2,0):1},{(1,1):2},{(0,2):1}]),
 ('unit_two_variables',2,[{(0,0):1}])]
N=8;reports=[];cells=0;strict=0
for name,q,gens in cases:
    for p in [0,2,3]:
        actual,reduce=quotient(q,gens,p,N)
        h=[len(d['std'])for d in actual];lex,lex_reduce=lex_quotient(q,h,N)
        b=[graded_betti(q,actual,reduce,p,j)for j in range(N+1)]
        lb=[graded_betti(q,lex,lex_reduce,p,j)for j in range(N+1)]
        for a,l in zip(b,lb):
            assert all(x>=0 for x in a+l)
            for x,y in zip(a,l):assert x<=y;cells+=1;strict+=x<y
        generators=[]
        for n in range(N+1):
            ideal=set(lex[n]['mons'])-set(lex[n]['std'])
            for a in ideal:
                parents=[tuple(v-(i==x)for i,v in enumerate(a))for x in range(q)if a[x]]
                if all(v in lex[n-1]['std']for v in parents):generators.append(a)
        # Unit ideals are separate: max(1) must not enter the proper-ideal EK formula.
        if h[0]:
            from math import comb
            for j in range(N+1):
                for i in range(1,q+2):
                    predicted=sum(comb(max(k for k,v in enumerate(a)if v),i-1)
                        if i-1<=max(k for k,v in enumerate(a)if v) else 0
                        for a in generators if sum(a)+i-1==j)
                    assert predicted==lb[j][i]
        reports.append(dict(name=name,q=q,characteristic=p,Hilbert=h,actual_graded_Betti=b,
            lex_graded_Betti=lb,lex_generators=generators))
sensitive={r['characteristic']:r for r in reports if r['name']=='characteristic_sensitive'}
assert sensitive[2]['Hilbert']!=sensitive[3]['Hilbert']
assert strict>0
result=dict(status='PASS_INDEPENDENT_FINITE_GRADED_MODELS',cases=len(reports),internal_degrees=[0,N],
    characteristics=[0,2,3],comparison_cells=cells,strict_comparison_cells=strict,
    characteristic_sensitive_Hilbert_confirmed=True,scope='Finite exact ideal-piece and actual quotient-action computations; no project imports or cross-characteristic rank assumption; not a universal theorem',reports=reports)
if out is not None:
    out.parent.mkdir(parents=True,exist_ok=True)
    with out.open('x')as f:f.write(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items()if k!='reports'},indent=2))
