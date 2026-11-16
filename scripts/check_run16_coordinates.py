#!/usr/bin/env python3
"""Independent exact finite regressions; universal proofs live in Lean."""
from fractions import Fraction
from itertools import combinations
from math import gcd
from pathlib import Path
import json,time
ROOT=Path(__file__).resolve().parents[1]
def minimal(points):
    pts=set(points)
    return sorted(p for p in pts if not any(q!=p and q[0]<=p[0] and q[1]<=p[1] for q in pts))
def above(p,gens): return any(a<=p[0] and b<=p[1] for a,b in gens)
def rank(mat,p):
    if not mat:return 0
    a=[[v%p if p else Fraction(v) for v in row]for row in mat];r=0
    for j in range(len(a[0])):
        z=next((i for i in range(r,len(a))if a[i][j]),None)
        if z is None:continue
        a[r],a[z]=a[z],a[r];iv=pow(a[r][j],-1,p)if p else 1/a[r][j]
        a[r]=[(v*iv)%p if p else v*iv for v in a[r]]
        for i in range(len(a)):
            if i==r or not a[i][j]:continue
            c=a[i][j];a[i]=[(v-c*w)%p if p else v-c*w for v,w in zip(a[i],a[r])]
        r+=1
        if r==len(a):break
    return r

def check(m,d,a,u,matrices=False):
    offsets=[0,*a,u];sums=[{0}]
    for n in range(2*u+1):sums.append({b+c for b in offsets for c in sums[-1]})
    def inside(r,L,K):return r+u*K in sums[L+K+(r!=0)]
    mins=[[(L,K)for L in range(u)for K in range(u)if inside(r,L,K)and (L==0 or not inside(r,L-1,K))and (K==0 or not inside(r,L,K-1))]for r in range(u)]
    stop=(u-2)//2+u//gcd(m,u)
    def start(r,j,c):
        s=(r+j*m)%u;carry=(r+j*m)//u
        return s,(max(0,c[0]-j*d-carry+(r!=0)-(s!=0)),c[1]+carry)
    tg=[[]for _ in range(u)]
    for r in range(u):
        for j in range(1,stop+1):
            for c in mins[r]:s,p=start(r,j,c);tg[s].append(p)
    tg=[minimal(row)for row in tg]
    ng=[minimal((max(L,A),max(K,B))for L,K in mins[r]for A,B in tg[r])for r in range(u)]
    def corner(p,gens):return not above(p,gens)and above((p[0]+1,p[1]),gens)and above((p[0],p[1]+1),gens)
    maxval=(m+u+u)*m+u*(m+u+1)*d+u*d+m
    gens=[m+b*d for b in offsets];orders=[None]*(maxval+1);orders[0]=0
    for x in range(1,maxval+1):
        lens=[orders[x-g]+1 for g in gens if x>=g and orders[x-g] is not None]
        if lens:orders[x]=max(lens)
    pc=sum(map(len,mins));pg=0;R=0
    for r in range(u):
        for L,K in mins[r]:
            n=L+K+(r!=0);x=n*m+(r+u*K)*d
            assert (not above((L,K),tg[r]))==(orders[x]==n)
            pg+=orders[x]==n
        for L in range(u):
            for K in range(m+u):
                inm=above((L,K),mins[r]);n=L+K+(r!=0);x=n*m+(r+u*K)*d
                if inm:assert above((L,K),ng[r])==(orders[x]>n)
                geom=inm and corner((L,K),ng[r])
                actual=inm and orders[x]==n and orders[x+m]>n+1 and orders[x+m+u*d]>n+1
                assert geom==actual
                R+=geom
    for r in range(u):
        for j in range(stop+1,stop+3*u//gcd(m,u)+6):
            for c in mins[r]:s,p=start(r,j,c);assert above(p,tg[s])
    W=1+sum(min(L+K+(r!=0)for L,K in mins[r])for r in range(u));H=max(L for row in mins for L,K in row)
    z=sum(len(row)-1 for row in tg);rh=min(W-u,u*max(H-2,0))
    assert 0<=R<=z<=W-u and R<=rh
    out=dict(m=m,d=d,a=a,u=u,PC=pc,PG=pg,R=R,W=W,Hx=H,Rhat=rh,stop=stop)
    if matrices:
        basis=[(L+K+(r!=0),r+u*K)for r,row in enumerate(mins)for L,K in row];idx={b:i for i,b in enumerate(basis)}
        q=len(a);ranks={p:[]for p in [0,2,3]}
        for i in range(1,q+1):
            src=list(combinations(range(q),i));dst=list(combinations(range(q),i-1));di={J:t for t,J in enumerate(dst)}
            mat=[[0]*(pc*len(src))for _ in range(pc*len(dst))]
            for j,J in enumerate(src):
                for b,(n,B)in enumerate(basis):
                    for t,v in enumerate(J):
                        dest=idx.get((n+1,B+a[v]))
                        if dest is not None:mat[di[J[:t]+J[t+1:]]*pc+dest][j*pc+b]+=(-1)**t
            for p in ranks:ranks[p].append(rank(mat,p))
        bettis={p:[pc-rr[0]]+[pc*__import__('math').comb(q,i)-rr[i-1]-(rr[i]if i<q else 0)for i in range(1,q+1)]for p,rr in ranks.items()}
        assert all(b[0]==1 for b in bettis.values())
        if q==2:
            sigma=sum(all((n+1,B+b)not in idx for b in a)for n,B in basis)
            assert all(b==[1,sigma+1,sigma]for b in bettis.values());out['sigma']=sigma
        out['QC_Betti_by_characteristic']=bettis
    return out

def main():
    start=time.monotonic();records=[]
    for u in range(3,8):
        for q in range(2,min(4,u-1)+1):
            for a in combinations(range(1,u),q):
                if gcd(gcd(*a),u)!=1:continue
                for m in range(u+1,u+5):
                    for d in [1,2,3]:
                        if gcd(m,d)==1:records.append(check(m,d,list(a),u))
    examples=[check(m,d,a,u,True)for m,d,a,u in [(6,1,[1,3],4),(7,2,[1,3],4),(7,1,[1,5],6),(9,1,[2,3,4],7),(8,1,[1,2],5),(8,1,[3,4],5)]]
    assert [(r['PC'],r['PG'],r['R'])for r in examples[:3]]==[(5,4,0),(5,5,0),(9,6,1)]
    assert examples[-2]['Hx']!=examples[-1]['Hx']
    result=dict(status='PASS_FINITE_REGRESSIONS_NOT_UNIVERSAL_PROOF',grid_count=len(records),seconds=round(time.monotonic()-start,3),examples=examples,grid=records)
    out=ROOT/'verification/run16/coordinate_model.json';out.write_text(json.dumps(result,indent=2)+'\n');print(result['status'],len(records),'cases',result['seconds'],'seconds')
if __name__=='__main__':main()
