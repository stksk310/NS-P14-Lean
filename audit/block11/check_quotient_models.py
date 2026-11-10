#!/usr/bin/env python3
"""Independent finite checks of N/Q, inherited degrees and both product-killing conditions."""
from functools import reduce
from itertools import product
from math import gcd
from pathlib import Path
from random import Random
import json

models={(1,),(2,3),(3,4),(4,5,11),(5,6,9),(6,7,15)}
for m in range(2,9):
    models.add(tuple(range(m,2*m)))
    models.update((m,g) for g in range(m+1,m+11) if gcd(m,g)==1)
    models.update((m,g,h) for g in range(m+1,m+7) for h in range(g+1,m+11)
                  if reduce(gcd,(m,g,h))==1)
rng=Random(1411)
counts=dict(models=0,apery_basis_vectors=0,hilbert_degree_checks=0,
            low_degree_isomorphism_checks=0,nonapery_ideal_product_checks=0,
            quotient_product_and_representative_checks=0,homogeneous_projection_checks=0,
            live_atomic_prefix_checks=0,apery_sum_nonadditive_pairs=0,
            additive_nonapery_head_products=0,degree_three_noninjective_models=0)
anchors={}
for generators in sorted(models):
    m=min(generators)
    def data(N):
        order=[None]*(N+1); word=[None]*(N+1)
        order[0]=0; word[0]=()
        for x in range(1,N+1):
            opts=[(order[x-g]+1,g) for g in generators if x>=g and order[x-g] is not None]
            if opts:
                order[x],g=max(opts)
                word[x]=word[x-g]+(g,)
        return order,word
    order,word=data(600)
    C=next(c for c in range(602-m) if all(order[x] is not None for x in range(c,c+m)))
    N=max(600,5*(C+1))
    if N>600: order,word=data(N)
    member=lambda x: 0<=x<=N and order[x] is not None
    assert all(member(x) for x in range(C,N+1))
    apery={next(x for x in range(C+m) if member(x) and x%m==r) for r in range(m)}
    atom_bound=max(m,C+m-1)
    atoms={x for x in range(1,atom_bound+1) if member(x)
           and not any(member(y) and member(x-y) for y in range(1,x))}
    e=len(atoms); delta=m-e
    def head(x): return member(x) and not (x>=m and member(x-m) and order[x]==order[x-m]+1)
    def aproj(f): return {x:c for x,c in f.items() if x in apery}
    def hproj(f): return {x:c for x,c in f.items() if head(x)}
    def homogeneous(f,n): return {x:c for x,c in f.items() if order[x]==n}
    def add(f,g,q):
        h=f.copy()
        for x,c in g.items(): h[x]=(h.get(x,0)+c)%q
        return {x:c for x,c in h.items() if c}
    def gmul(f,g,q):
        h={}
        for x,c in f.items():
            for y,d in g.items():
                if order[x+y]==order[x]+order[y]: h[x+y]=(h.get(x+y,0)+c*d)%q
        return {x:c for x,c in h.items() if c}
    def amul(f,g,q): return hproj(gmul(f,g,q))
    def qmul(f,g,q): return aproj(gmul(f,g,q))
    nu=max(order[x] for x in apery)
    hilbert=[sum(order[x]==n for x in apery) for n in range(nu+1)]
    assert len(apery)==m and hilbert[0]==1 and sum(hilbert)==m
    assert (hilbert[1] if len(hilbert)>1 else 0)==e-1
    assert all(hilbert) and sum(hilbert[2:])==delta and nu<=delta+1
    for n in range(delta+4):
        qbasis={x for x in apery if order[x]==n}
        assert len(qbasis)==(hilbert[n] if n<len(hilbert) else 0)
        assert bool(qbasis)==(n<=nu)
        counts['hilbert_degree_checks']+=1
    # Each A_n for n<=3 is complete inside this conductor-based bound.
    for n in range(4):
        abasis={x for x in range((n+1)*(C+1)) if head(x) and order[x]==n}
        qbasis={x for x in apery if order[x]==n}
        assert qbasis<=abasis
        assert all(x not in apery for x in abasis-qbasis)
        if n<=2:
            assert abasis==qbasis
            counts['low_degree_isomorphism_checks']+=1
        elif abasis!=qbasis:
            counts['degree_three_noninjective_models']+=1
    for w in apery:
        assert all(a in atoms-{m} for a in word[w])
        v=0
        for i,a in enumerate(word[w],1):
            assert v in apery and v+a in apery
            assert order[v+a]==order[v]+order[a]==i
            v+=a
            counts['live_atomic_prefix_checks']+=1
        assert v==w and len(word[w])==order[w]
        counts['apery_basis_vectors']+=1
    for x,y in product(sorted(apery),repeat=2):
        if x+y in apery and order[x+y]>order[x]+order[y]:
            counts['apery_sum_nonadditive_pairs']+=1
        if head(x+y) and x+y not in apery and order[x+y]==order[x]+order[y]:
            counts['additive_nonapery_head_products']+=1
    # Full coefficient computations on a finite head prefix, allowing mixed degrees.
    heads=[x for x in range(121) if head(x)]
    nheads=[x for x in heads if x not in apery]
    for q in (2,4,5):
        for _ in range(20):
            def sample(exps):
                return {x:c for x in rng.sample(exps,min(7,len(exps))) if (c:=rng.randrange(q))}
            a,b,n,n2=sample(heads),sample(heads),sample(nheads),sample(nheads)
            assert not aproj(n)
            assert not aproj(amul(a,n,q))
            counts['nonapery_ideal_product_checks']+=1
            actual=aproj(amul(a,b,q))
            assert actual==qmul(aproj(a),aproj(b),q)
            assert aproj(amul(add(a,n,q),add(b,n2,q),q))==actual
            counts['quotient_product_and_representative_checks']+=1
            for degree in range(nu+4):
                assert aproj(homogeneous(a,degree))==homogeneous(aproj(a),degree)
                assert not aproj(homogeneous(n,degree))
                counts['homogeneous_projection_checks']+=1
    if generators in {(1,),(3,4,5),(4,5,11),(5,6,9),(6,7,15)}:
        anchors[','.join(map(str,generators))]={'multiplicity':m,'least_conductor':C,
            'apery':sorted(apery),'atoms':sorted(atoms),'embedding_dimension':e,
            'deficit':delta,'top_degree':nu,'hilbert_function':hilbert,
            'nonapery_heads_through_120':nheads}
    if generators==(5,6,9):
        assert 18 in apery and order[9]==1 and order[18]==3
        assert qmul({9:1},{9:1},5)=={} and aproj({18:1})=={18:1}
    if generators==(4,5,11):
        assert head(15) and 15 not in apery and order[15]==3
        assert amul({5:1},{10:1},5)=={15:1} and qmul({5:1},{10:1},5)=={}
    counts['models']+=1
assert counts['apery_sum_nonadditive_pairs']>0 and counts['additive_nonapery_head_products']>0
assert anchors['3,4,5']['apery']==[0,4,5] and anchors['3,4,5']['hilbert_function']==[1,2]
assert anchors['4,5,11']['apery']==[0,5,10,11] and anchors['4,5,11']['hilbert_function']==[1,2,1]
record={'status':'PASS','seed':1411,'coefficient_rings':['Z/2Z','Z/4Z','Z/5Z'],
        'counts':counts,'anchors':anchors,
        'scope':'Supplementary exact finite computations. A is obtained by removing live incoming coordinates; N is non-Apery head support and Q is the actual two-stage coordinate quotient. Products, changed representatives, inherited degree restrictions, Hilbert counts and live atomic generation paths are checked independently. These computations do not prove general Lean theorems, completed-ring comparison, or global finiteness of A, N or T.'}
Path(__file__).with_name('quotient_finite_checks.json').write_text(json.dumps(record,indent=2)+'\n')
print('PASS',counts)
