#!/usr/bin/env python3
"""Independent finite coordinate, stratum-action and formal-prefix checks; not universal proofs."""
from functools import reduce
from itertools import product
from math import gcd
from pathlib import Path
from random import Random
import json

models={(1,),(2,3),(3,4),(4,5,11),(5,6,13),(9,10,15,26)}
for m in range(2,9):
    models.add(tuple(range(m,2*m)))
    models.update((m,g) for g in range(m+1,m+11) if gcd(m,g)==1)
    models.update((m,g,h) for g in range(m+1,m+7) for h in range(g+1,m+11)
                  if reduce(gcd,(m,g,h))==1)
rng=Random(1412)
counts=dict(models=0,terminal_jump_bounds=0,filtration_action_checks=0,
            same_jump_action_checks=0,nonzero_same_jump_actions=0,
            degree_shift_checks=0,live_split_checks=0,
            formal_factorization_coefficients=0,formal_truncation_coefficients=0,
            formal_product_comparisons=0,formal_product_coefficient_checks=0)
anchors={}
N=800; L=160
for gs in sorted(models):
    m=min(gs); o=[None]*(N+1); words=[None]*(N+1);o[0]=0;words[0]=()
    for v in range(1,N+1):
        opts=[(o[v-g]+1,g) for g in gs if g<=v and o[v-g] is not None]
        if opts:
            o[v],g=max(opts);words[v]=words[v-g]+(g,)
    member=lambda v: 0<=v<=N and o[v] is not None
    C=next(c for c in range(N-m+2) if all(member(v) for v in range(c,c+m)))
    apery={next(v for v in range(C+m) if member(v) and v%m==r) for r in range(m)}
    nu=max(o[v] for v in apery)
    atom_bound=max(m,C+m-1)
    atoms={v for v in range(1,atom_bound+1) if member(v)
           and not any(member(a) and member(v-a) for a in range(1,v))}
    e=len(atoms);delta=m-e
    nonx=sorted(atoms-{m})
    def jump(v): return o[v+m]-o[v]
    def terminal(v): return member(v) and jump(v)>=2
    def head(v): return member(v) and not (v>=m and member(v-m) and o[v]==o[v-m]+1)
    ts=[v for v in range(121) if terminal(v)]
    for t in ts:
        assert 2<=jump(t)<=nu
        assert head(t+m) and t+m not in apery
        assert o[t+m]==o[t]+jump(t)
        counts['terminal_jump_bounds']+=1
    if delta==0: assert not ts and nu<=1
    def add(f,g,q):
        h=f.copy()
        for v,c in g.items(): h[v]=(h.get(v,0)+c)%q
        return {v:c for v,c in h.items() if c}
    def gmul(f,g,q):
        h={}
        for v,c in f.items():
            for w,d in g.items():
                if o[v+w]==o[v]+o[w]: h[v+w]=(h.get(v+w,0)+c*d)%q
        return {v:c for v,c in h.items() if c}
    def hproj(f): return {v:c for v,c in f.items() if head(v)}
    def toheads(f): return {t+m:c for t,c in f.items()}
    def fromheads(f):
        assert all(head(y) and y not in apery and y>=m and terminal(y-m) for y in f)
        return {y-m:c for y,c in f.items()}
    def exact(f,s): return {t:c for t,c in f.items() if jump(t)==s}
    def polynomial(q):
        # Explicit evaluation of a polynomial in the actual non-x atoms.
        f={}
        for _ in range(4):
            w=[rng.choice(nonx) for _ in range(rng.randrange(4))] if nonx else []
            a={0:rng.randrange(q)}
            for g in w: a=gmul(a,{g:1},q)
            f=add(f,a,q)
        return f
    for q in (2,4,5):
        for s in range(1,nu+2):
            for _ in range(6):
                f={t:c for t in rng.sample(ts,min(6,len(ts))) if (c:=rng.randrange(q))}
                p=polynomial(q)
                d={t:c for t,c in f.items() if jump(t)>=s}
                a=toheads({t:c for t,c in f.items() if jump(t)<=s})
                dout=gmul(p,d,q)
                aout=hproj(gmul(hproj(p),a,q))
                assert all(terminal(t) and jump(t)>=s for t in dout)
                at=fromheads(aout)
                assert all(jump(t)<=s for t in at)
                assert exact(dout,s)==exact(at,s)
                counts['filtration_action_checks']+=2
                counts['same_jump_action_checks']+=1
                counts['nonzero_same_jump_actions']+=bool(exact(dout,s))
                for t in exact(dout,s):
                    assert o[t+m]==o[t]+s
                    counts['degree_shift_checks']+=1
    # Formal-series prefix checks through exponent L. The coefficient prescription
    # is evaluated on all indices in the prefix, including zero coefficients.
    for n in range(5):
        prefixes={}
        for v in range(L+1):
            if member(v) and o[v]>=n:
                u=sum(words[v][:n]);w=v-u
                assert member(u) and member(w) and o[u]==n and o[w]==o[v]-n
                prefixes[v]=(u,w)
                counts['live_split_checks']+=1
        for q in (1,2,4,5):
            f={v:(v*v+2*v+17)%q for v in prefixes}
            groups={}
            for v,(u,w) in prefixes.items(): groups.setdefault(u,{})[w]=f[v]
            for v in range(L+1):
                rebuilt=sum(g.get(v-u,0) for u,g in groups.items() if u<=v)%q
                assert rebuilt==f.get(v,0)
                trunc=f.get(v,0) if member(v) and o[v]==n else 0
                if member(v) and o[v]<n+1: assert (f.get(v,0)-trunc)%q==0
                counts['formal_factorization_coefficients']+=1
                counts['formal_truncation_coefficients']+=1
    def conv(f,g,q):
        h={}
        for v,c in f.items():
            for w,d in g.items():
                if v+w<=L: h[v+w]=(h.get(v+w,0)+c*d)%q
        return {v:c for v,c in h.items() if c}
    for n,p,q in product(range(3),range(3),(2,4,5)):
        f={v:(v+3)%q for v in range(L+1) if member(v) and o[v]>=n}
        g={v:(v*v+1)%q for v in range(L+1) if member(v) and o[v]>=p}
        fg=conv(f,g,q)
        assert all(o[v]>=n+p for v in fg)
        exact_product={v:c for v,c in fg.items() if o[v]==n+p}
        ft={v:c for v,c in f.items() if o[v]==n}
        gt={v:c for v,c in g.items() if o[v]==p}
        finite_product={v:c for v,c in gmul(ft,gt,q).items() if v<=L}
        assert exact_product==finite_product
        counts['formal_product_comparisons']+=1
        counts['formal_product_coefficient_checks']+=L+1
    if gs==(5,6,13):
        assert jump(13)==jump(19)==2
        assert gmul({6:1},{13:1},5)=={19:1}
        assert hproj(gmul({6:1},{18:1},5))=={24:1}
    if gs==(9,10,15,26):
        assert jump(26)==2 and jump(41)==3
        assert gmul({15:1},{26:1},5)=={41:1}
        assert hproj(gmul({15:1},{35:1},5))=={}
        assert head(50) and 50 not in apery
    if gs in {(1,),(3,4),(4,5,11),(5,6,13),(9,10,15,26)}:
        anchors[','.join(map(str,gs))]={'least_conductor':C,'multiplicity':m,
            'apery':sorted(apery),'top_degree':nu,'deficit':delta,
            'terminal_jumps_through_120':{str(t):jump(t) for t in ts}}
    counts['models']+=1
assert counts['nonzero_same_jump_actions']>0
record={'status':'PASS','seed':1412,'counts':counts,'anchors':anchors,
        'scope':'Independent exact finite checks on 279 semigroups. Formal-series identities are checked coefficientwise only through exponent160, including a zero coefficient ring; Lean separately proves actual infinite-series identities. Stratum action tests use polynomial evaluation in actual non-x atoms over Z/2Z,Z/4Z,Z/5Z, including nonzero same-jump actions and a failure of unrestricted coordinate S0-linearity. No global finiteness or P14/Tor conclusion is inferred.'}
Path(__file__).with_name('run12_finite_checks.json').write_text(json.dumps(record,indent=2)+'\n')
print('PASS',counts)
