#!/usr/bin/env python3
"""Finite, independent semigroup-ideal and quotient-product checks (not a universal proof)."""
from functools import reduce
from itertools import product
from math import gcd
from pathlib import Path
from random import Random
import json

models = {(1,), (2, 3), (3, 4), (6, 7, 15), (4, 5, 11)}
for m in range(2, 9):
    models.add(tuple(range(m, 2*m)))
    models.update((m,g) for g in range(m+1,m+11) if gcd(m,g)==1)
    models.update((m,g,h) for g in range(m+1,m+7) for h in range(g+1,m+11)
                  if reduce(gcd,(m,g,h))==1)
rng = Random(1409)
counts = dict(models=0, ideal_power_membership_checks=0, degree_sets=0,
              polynomial_quotient_products=0, representative_changes=0,
              x_action_kernel_checks=0, nonadditive_unit_products=0,
              nonzero_products=0)
anchors = {}

def add(f,g,q):
    h=f.copy()
    for x,c in g.items(): h[x]=(h.get(x,0)+c)%q
    return {x:c for x,c in h.items() if c}

def multiply(f,g,q):
    h={}
    for x,c in f.items():
        for y,d in g.items(): h[x+y]=(h.get(x+y,0)+c*d)%q
    return {x:c for x,c in h.items() if c}

for generators in sorted(models):
    m=min(generators)
    reachable=[False]*601
    reachable[0]=True
    for x in range(1,601):
        reachable[x]=any(x>=g and reachable[x-g] for g in generators)
    C=next(c for c in range(602-m) if all(reachable[c:c+m]))
    N=max(250,9*(C+1))
    reachable=[False]*(N+1)
    reachable[0]=True
    order=[None]*(N+1)
    order[0]=0
    for x in range(1,N+1):
        lengths=[order[x-g]+1 for g in generators if x>=g and order[x-g] is not None]
        if lengths:
            reachable[x]=True
            order[x]=max(lengths)
    assert all(reachable[C:])
    positive=[x for x in range(1,N+1) if reachable[x]]
    # Actual monomial-ideal exponent sets: I_0=S, I_(n+1)=I_n+(S\{0}).
    # Boolean convolution uses ALL positive semigroup elements, independently
    # of the generator-factorization DP used above to compute order.
    mask=(1<<(N+1))-1
    powers=[sum(1<<x for x in range(N+1) if reachable[x])]
    for n in range(1,10):
        bits=0
        for a in positive: bits |= powers[-1]<<a
        powers.append(bits & mask)
    for n,bits in enumerate(powers):
        for x in range(N+1):
            assert bool((bits>>x)&1)==(order[x] is not None and n<=order[x])
            counts['ideal_power_membership_checks']+=1
    for n in range(9):
        exact={x for x in range(N+1) if (powers[n]>>x)&1 and not (powers[n+1]>>x)&1}
        assert exact=={x for x in range(N+1) if order[x]==n}
        assert all(x<(n+1)*(C+1) for x in exact)
        # N>=9(C+1) makes this a complete degree set, not a truncated one.
        counts['degree_sets']+=1
    def project(f,n): return {x:c for x,c in f.items() if order[x]==n}
    def sample(n,q):
        exps=[x for x in range(61) if order[x] is not None and order[x]>=n]
        assert exps
        return {x:c for x in rng.sample(exps,min(6,len(exps))) if (c:=rng.randrange(q))}
    for q,n,p in product((2,4,5),range(4),range(4)):
        for _ in range(4):
            f,g,u,v=sample(n,q),sample(p,q),sample(n+1,q),sample(p+1,q)
            actual=project(multiply(f,g,q),n+p)
            coordinate={}
            for x,c in project(f,n).items():
                for y,d in project(g,p).items():
                    if order[x+y]==n+p:
                        coordinate[x+y]=(coordinate.get(x+y,0)+c*d)%q
                    else:
                        assert order[x+y]>n+p
                        counts['nonadditive_unit_products']+=1
            coordinate={x:c for x,c in coordinate.items() if c}
            assert actual==coordinate
            assert project(multiply(add(f,u,q),add(g,v,q),q),n+p)==actual
            counts['polynomial_quotient_products']+=1
            counts['representative_changes']+=1
            counts['nonzero_products']+=bool(actual)
            for a,degree in ((project(f,n),n),(project(g,p),p)):
                image=project(multiply(a,{m:1},q),degree+1)
                terminals={x:c for x,c in a.items() if order[x+m]>degree+1}
                assert (image=={})==(a==terminals)
                counts['x_action_kernel_checks']+=1
    if generators in {(1,),(2,3),(4,5,11),(6,7,15)}:
        anchors[','.join(map(str,generators))]={'least_conductor':C,
            'degree_exponents_0_to_3':[[x for x in range(N+1) if order[x]==n] for n in range(4)]}
    counts['models']+=1
assert multiply({1:1,2:1},{1:1,2:1},2)=={2:1,4:1} # cancellation in characteristic two
assert multiply({1:2},{1:2},4)=={} # nilpotent coefficients over a non-domain
assert counts['nonadditive_unit_products']>0 and counts['nonzero_products']>0
record={'status':'PASS','seed':1409,'coefficient_rings':['Z/2Z','Z/4Z','Z/5Z'],
        'counts':counts,'anchors':anchors,
        'scope':'Supplementary finite exact computations. Actual ideal exponent powers use Boolean convolutions of all positive semigroup elements; order uses a separate factorization DP. Polynomial convolution is compared with exact-order quotient coordinates and changed representatives. No claim of completed-ring equivalence or universal kernel-basis formalization.'}
Path(__file__).with_name('ring_finite_checks.json').write_text(json.dumps(record,indent=2)+'\n')
print('PASS',counts)
