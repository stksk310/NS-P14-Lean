#!/usr/bin/env python3
"""Independent exact finite regressions, never a premise of the Lean proof."""
from pathlib import Path
from math import comb,gcd
import argparse,json
ROOT=Path(__file__).resolve().parents[1]
def choose(n,k):return comb(n,k) if 0<=k<=n else 0
def profile(m,v,i):
    if i==0:return 1
    defect=v-(m-1)%v
    return i*choose(v,i+1)+((defect+1-i)*choose(v,i-1) if i<=defect else (i-defect)*choose(v,i))
def check():
    count=0
    for e in range(1,25):
        for m in range(e,80):
            for w in range(m+5):
                tags=[e==1,e==2,e==3,e>=4 and m-1<=w,e==4 and w<=m-2,e>=5 and w<=m-2]
                assert sum(tags)==1,(e,m,w,tags);count+=1
    ranks=0
    for e in range(4,60):
        for r in range(2,e):
            assert r==2 or r==3 or 4<=r<=8 or 9<=r
            assert r<9 or e>=10;ranks+=1
    normalized=0
    for e in range(6,30):
        for u in range(e-1,120):
            assert (u==e-1)+(u==e)+(e+1<=u<=2*e-3)+(u>=2*e-2)==1;normalized+=1
    profiles=0
    for m in range(2,50):
        for v in range(1,m):
            for i in range(m+2):
                b=profile(m,v,i);assert b>=0
                if v==m-1 and i>0:assert b==i*choose(m,i+1)
                if i>v:assert b==0
                profiles+=1
    assert profile(6,5,5)==5
    physical=[(17,3,5),(20,3,6),(23,3,7),(26,3,8),(29,3,9),(32,3,10)]
    assert all(m==d*u+2 and gcd(m,d)==1 and min(d*u,m-1)==d*u and d*u!=u for m,d,u in physical)
    fixtures=[('N',[1],1,0),('two',[2,3],2,1),('two_nonunit',[3,5],2,2),('three_narrow',[4,5,6],3,2),('three_wide',[4,5,7],3,3),('four_narrow',[6,7,9,10],4,4),('four_ordinary',[6,7,9,11],4,5)]
    for _,atoms,e,w in fixtures:assert len(atoms)==e and max(atoms)-min(atoms)==w
    return {'status':'PASS_RUN20_EXACT_REGRESSION','partition_cases':count,'rank_cases':ranks,'normalized_width_cases':normalized,'AP_profile_rows':profiles,'physical_dilations':physical,'actual_atom_fixtures':fixtures,'ordinary_target_beta5':5,'scope':'finite regression only; universal mathematical closure is Lean'}
def main():
    p=argparse.ArgumentParser();p.add_argument('--output',required=True);a=p.parse_args()
    from verify_run20 import safe
    out=safe(ROOT,a.output)
    if out.exists() or Path(a.output).parts[:3]!=('verification','run20','runs'):p.error('new Run20 output required')
    result=check()
    with out.open('x') as f:json.dump(result,f,ensure_ascii=False,indent=2);f.write('\n')
    print(result['status'],result['partition_cases'],result['AP_profile_rows'])
if __name__=='__main__':main()
