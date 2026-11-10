#!/usr/bin/env python3
"""Independent finite checks of global products, full-support kernels and head quotients."""
from functools import reduce
from itertools import product
from math import gcd
from pathlib import Path
from random import Random
import json

models={(1,),(2,3),(3,4),(4,5,11),(6,7,15)}
for m in range(2,9):
    models.add(tuple(range(m,2*m)))
    models.update((m,g) for g in range(m+1,m+11) if gcd(m,g)==1)
    models.update((m,g,h) for g in range(m+1,m+7) for h in range(g+1,m+11)
                  if reduce(gcd,(m,g,h))==1)
rng=Random(1410)
counts=dict(models=0,monomial_associativity_checks=0,mixed_polynomial_ring_checks=0,
            exhaustive_coefficient_vectors=0,kernel_checks=0,range_preimage_checks=0,
            head_quotient_product_checks=0,terminal_coordinates_in_prefix=0,
            nonapery_head_coordinates_in_prefix=0)
anchors={}
N=600
for generators in sorted(models):
    m=min(generators)
    order=[None]*(N+1); order[0]=0
    for x in range(1,N+1):
        ls=[order[x-g]+1 for g in generators if x>=g and order[x-g] is not None]
        if ls: order[x]=max(ls)
    member=lambda x: 0<=x<=N and order[x] is not None
    C=next(c for c in range(N-m+2) if all(member(x) for x in range(c,c+m)))
    assert all(member(x) for x in range(C,N+1))
    def live(x): return order[x+m]==order[x]+1
    def terminal(x): return member(x) and not live(x)
    def head(y): return member(y) and not (y>=m and member(y-m) and live(y-m))
    def shift(f): return {x+m:c for x,c in f.items() if live(x)}
    def headpart(f): return {x:c for x,c in f.items() if head(x)}
    def preimage(f):
        assert all(not head(y) for y in f)
        result={y-m:c for y,c in f.items()}
        assert all(member(x) and live(x) for x in result)
        return result
    def add(f,g,q):
        h=f.copy()
        for x,c in g.items(): h[x]=(h.get(x,0)+c)%q
        return {x:c for x,c in h.items() if c}
    def scale(c,f,q): return {x:d for x,a in f.items() if (d:=c*a%q)}
    def mul(f,g,q):
        h={}
        for x,c in f.items():
            for y,d in g.items():
                if order[x+y]==order[x]+order[y]:
                    h[x+y]=(h.get(x+y,0)+c*d)%q
        return {x:c for x,c in h.items() if c}
    def ordinary_mul(f,g,q):
        h={}
        for x,c in f.items():
            for y,d in g.items(): h[x+y]=(h.get(x+y,0)+c*d)%q
        return {x:c for x,c in h.items() if c}
    # A second product groups into homogeneous ideal-power quotients, multiplies
    # ordinary polynomial representatives, then extracts the degree-sum layer.
    def quotient_product(f,g,q):
        h={}
        for n in {order[x] for x in f}:
            a={x:c for x,c in f.items() if order[x]==n}
            for p in {order[y] for y in g}:
                b={y:c for y,c in g.items() if order[y]==p}
                piece={z:c for z,c in ordinary_mul(a,b,q).items() if order[z]==n+p}
                h=add(h,piece,q)
        return h
    exponents=[x for x in range(61) if member(x)]
    terminals=[x for x in range(121) if terminal(x)]
    heads=[x for x in range(121) if head(x)]
    apery={next(x for x in range(C+m) if member(x) and x%m==r) for r in range(m)}
    counts['terminal_coordinates_in_prefix']+=len(terminals)
    counts['nonapery_head_coordinates_in_prefix']+=sum(y not in apery for y in heads)
    # Finite exponent tests; no global finiteness of T or the head index set is asserted.
    small=exponents[:12]
    for x,y,z in product(small,repeat=3):
        assert mul(mul({x:1},{y:1},5),{z:1},5)==mul({x:1},mul({y:1},{z:1},5),5)
        counts['monomial_associativity_checks']+=1
    core=list(dict.fromkeys(([terminals[0]] if terminals else [])+[0,m]+exponents[1:]))[:4]
    for q in (2,4,5):
        for coeffs in product(range(q),repeat=len(core)):
            f={x:c for x,c in zip(core,coeffs) if c}
            image=shift(f)
            assert (image=={})==all(terminal(x) for x in f)
            # Head restriction has exactly the live-shift image as its kernel.
            if headpart(f)=={}:
                assert shift(preimage(f))==f
                counts['range_preimage_checks']+=1
            counts['kernel_checks']+=1
            counts['exhaustive_coefficient_vectors']+=1
        for _ in range(12):
            def sample():
                return {x:c for x in rng.sample(exponents,min(7,len(exponents)))
                        if (c:=rng.randrange(q))}
            f,g,h,u,v=sample(),sample(),sample(),sample(),sample()
            fg=mul(f,g,q)
            assert fg==quotient_product(f,g,q)
            assert mul(f,g,q)==mul(g,f,q)
            assert mul(fg,h,q)==mul(f,mul(g,h,q),q)
            assert mul(f,add(g,h,q),q)==add(mul(f,g,q),mul(f,h,q),q)
            assert mul({0:1},f,q)==f and mul(f,{0:1},q)==f
            c=rng.randrange(q)
            assert mul({0:c},f,q)==scale(c,f,q)
            assert mul(f,{m:1},q)==shift(f)
            assert (shift(f)=={})==all(terminal(x) for x in f)
            counts['kernel_checks']+=1
            # Lift the complete non-head part through an actual live predecessor.
            incoming={x:c for x,c in f.items() if not head(x)}
            assert shift(preimage(incoming))==incoming
            counts['range_preimage_checks']+=1
            # Changing either ring representative by x times any element does
            # not change its class or the product's class in the principal quotient.
            assert headpart(add(f,shift(u),q))==headpart(f)
            assert headpart(mul(add(f,shift(u),q),add(g,shift(v),q),q))==headpart(fg)
            counts['head_quotient_product_checks']+=1
            counts['mixed_polynomial_ring_checks']+=1
    if generators in {(1,),(2,3),(4,5,11),(6,7,15)}:
        anchors[','.join(map(str,generators))]={'least_conductor':C,
            'terminal_prefix':terminals,'head_prefix':heads,'checked_exponents_through':120,
            'nonapery_heads_prefix':[y for y in heads if y not in apery]}
    counts['models']+=1
assert anchors['1']['terminal_prefix']==[] and anchors['1']['head_prefix']==[0]
assert 11 in anchors['4,5,11']['terminal_prefix'] and 15 in anchors['4,5,11']['nonapery_heads_prefix']
record={'status':'PASS','seed':1410,'coefficient_rings':['Z/2Z','Z/4Z','Z/5Z'],
        'counts':counts,'anchors':anchors,
        'scope':'Supplementary exact finite computations, not a proof over all exponents or semigroups. Global multiplication is independently compared with degreewise multiplication of polynomial representatives. Kernels include exhaustive coefficient vectors, with explicit live-predecessor lifts for the image. Head-quotient products are invariant under adding actual x multiples. No completion comparison or global finiteness of T/head sets is inferred.'}
Path(__file__).with_name('tangent_finite_checks.json').write_text(json.dumps(record,indent=2)+'\n')
print('PASS',counts)
