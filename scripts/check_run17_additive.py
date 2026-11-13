#!/usr/bin/env python3
"""Independent finite regression; never used as the universal Lean proof."""
from itertools import combinations_with_replacement
from math import gcd
from functools import reduce
from pathlib import Path
import json

def residues(mask,u): return [i for i in range(u) if mask>>i&1]
def sumset(a,b,u):
    return sum(1<<i for i in {(x+y)%u for x in residues(a,u) for y in residues(b,u)})
def stabilizer(s,u):
    return sum(1<<h for h in range(u) if sumset(1<<h,s,u)==s)
def zsf(seq,u):
    sums={0}
    for a in seq:
        new={(s+a)%u for s in sums}
        if 0 in new:return False
        sums|=new
    return True

def main():
    counts=dict(kneser_pairs=0,iterated=0,proper_growth=0,four_point=0,
                zero_sum_free_multisets=0,long_multisets=0)
    for u in range(1,9):
        full=(1<<u)-1
        sets=range(1,full+1)
        stab={s:stabilizer(s,u)for s in sets}
        cache={}
        def add(a,b):
            key=tuple(sorted((a,b)))
            if key not in cache:cache[key]=sumset(a,b,u)
            return cache[key]
        for a in sets:
            for b in sets:
                s=add(a,b);h=stab[s]
                assert add(a,h).bit_count()+add(b,h).bit_count()<=s.bit_count()+h.bit_count()
                counts['kneser_pairs']+=1
        for a in sets:
            chain=[1]
            for n in range(1,u+3):chain.append(add(chain[-1],a))
            for n,s in enumerate(chain):
                assert n or s==1
                if n:
                    h=stab[s]
                    assert n*add(a,h).bit_count()<=s.bit_count()+(n-1)*h.bit_count()
                    counts['iterated']+=1
            aa=residues(a,u);ac=len(aa)
            if 0 not in aa or reduce(gcd,aa,u)!=1:continue
            for n in range(1,u+2):
                s=chain[n];t=chain[n+1]
                assert s.bit_count()>=min(u,ac+(n-1)*((ac+1)//2))
                if t!=full:
                    d=t.bit_count()-s.bit_count()
                    assert d>=(ac+1)//2
                    counts['proper_growth']+=1
                    if ac==4 and d<3:
                        h=stab[t]
                        assert h.bit_count()==2 and add(a,h)==a
                        assert any(u==2*m and a==sum(1<<x for x in [0,k,m,k+m])
                                   and gcd(k,m)==1 for m in range(1,u)for k in range(1,m))
                        counts['four_point']+=1
        units=[c for c in range(u)if gcd(c,u)==1]
        for length in range(1,u):
            for seq in combinations_with_replacement(range(1,u),length):
                if not zsf(seq,u):continue
                counts['zero_sum_free_multisets']+=1
                if u<2*length:
                    assert any(sum(c*a%u for a in seq)<u for c in units)
                    counts['long_multisets']+=1
    examples=[]
    for u,seq,c,target in [(6,[5,5,5,4],5,5),(9,[2,2,2,4,6],5,8)]:
        assert zsf(seq,u) and gcd(c,u)==1 and sum(c*a%u for a in seq)==target
        examples.append(dict(u=u,sequence=seq,unit=c,representative_sum=target))
    boundary=[sum(c*a%6 for a in [2,2,3])for c in [1,5]]
    assert zsf([2,2,3],6)and sorted(boundary)==[7,11]
    actual=[]
    for m,d,a,u in [(7,2,[1,3],4),(8,1,[2,3],6),(9,1,[2,3],7)]:
        alphabet={0,*a};reach={0};layers=[1];dist={0:0}
        for n in range(1,u+1):
            reach={(x+y)%u for x in reach for y in alphabet}
            layers.append(len(reach))
            for r in reach:dist.setdefault(r,n)
        w=1+sum(dist.values())
        assert len(dist)==u and w==1+sum(u-size for size in layers[:u])
        assert w<=u+sum(max(0,u-len(alphabet)-((len(alphabet)+1)//2)*j)for j in range(u))
        assert w<=1+u*u//4
        actual.append(dict(m=m,d=d,a=a,u=u,layers=layers,W=w))
    assert actual[1]['W']==10 and zsf([2,3],7)
    report=dict(status='PASS_FINITE_REGRESSION_ONLY',counts=counts,SC_examples=examples,
                boundary_representative_sums=boundary,actual_core=actual,
                universal_proof='Lean exports, not this finite search')
    out=Path(__file__).resolve().parents[1]/'verification/run17/additive_checks.json'
    out.parent.mkdir(parents=True,exist_ok=True)
    out.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,ensure_ascii=False))
if __name__=='__main__':main()
