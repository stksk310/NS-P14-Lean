"""Independent finite core/rank and bounded actual-socle observations.
No project code imports; not a universal theorem or full actual Betti computation.
"""
from fractions import Fraction
from itertools import combinations
from math import comb,gcd
from pathlib import Path
import argparse,json,time

parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--output',help='fresh JSON file; default prints summary only')
args=parser.parse_args()
output=Path(args.output)if args.output else None
if output is not None and output.exists():parser.error('existing audit evidence must not be overwritten')

def choose(n,i):return comb(n,i)if 0<=i<=n else 0

def rank(rows,char):
    if not rows:return 0
    a=[[x%char if char else Fraction(x)for x in r]for r in rows];n=0
    for c in range(len(a[0])):
        r=next((r for r in range(n,len(a))if a[r][c]),None)
        if r is None:continue
        a[n],a[r]=a[r],a[n]
        inv=pow(a[n][c],-1,char)if char else 1/a[n][c]
        for r in range(n+1,len(a)):
            f=a[r][c]*inv
            if char:f%=char
            if f:a[r]=[(x-f*y)%char if char else x-f*y for x,y in zip(a[r],a[n])]
        n+=1
        if n==len(a):break
    return n

def profile(offsets,u):
    whole=[{0}];pieces=[{0}]
    for n in range(1,u+1):
        prev=whole[-1];nxt={x+y for x in prev for y in [0,*offsets,u]}
        whole.append(nxt);pieces.append(nxt-prev-{x+u for x in prev})
    assert not pieces[u]
    P=sum(map(len,pieces));q=len(offsets)
    height=max(n-(b+u-1)//u for n,ps in enumerate(pieces)for b in ps)
    dist={0:0};reached={0}
    for n in range(1,u):
        reached={(r+a)%u for r in reached for a in [0,*offsets]}
        for r in reached:dist.setdefault(r,n)
    assert len(dist)==u
    W=1+sum(dist.values());assert P<=W
    ranks={c:[0]*(q+2)for c in [0,2,3]}
    for i in range(1,q+1):
        sw=list(combinations(range(q),i));tw=list(combinations(range(q),i-1))
        for n in range(u):
            src=[(b,J)for b in pieces[n]for J in sw]
            dst=[(b,J)for b in pieces[n+1]for J in tw];ix={p:j for j,p in enumerate(dst)}
            matrix=[[0]*len(src)for _ in dst]
            for col,(b,J)in enumerate(src):
                for j,x in enumerate(J):
                    row=ix.get((b+offsets[x],J[:j]+J[j+1:]))
                    if row is not None:matrix[row][col]+=(-1)**j
            for c in ranks:ranks[c][i]+=rank(matrix,c)
    betti={c:[P*choose(q,i)-rs[i]-rs[i+1]for i in range(q+1)]for c,rs in ranks.items()}
    assert all(b[0]==1 and all(x>=0 for x in b)and b[2]+1==b[1]+b[3]for b in betti.values())
    t=u-q-1
    if t<=q:assert W==q+1+2*t and height<=t
    if u==5:
        for b in betti.values():
            assert b[1]+P<=11 and b[2]+3*P<=25
            if offsets in [(1,2,4),(1,3,4)]:assert b[1]<=5 and b[3]+3<=P
    if u%2==0 and u>=8:
        h=u//2
        ts=[t for t in range(1,h)if tuple(sorted((t,h,t+h)))==offsets]
        if ts:
            t=ts[0]
            expect={(0,0),(1,h)}|{(n,n*t+j*h)for n in range(1,h)for j in range(n+1)}
            actual={(n,b)for n,ps in enumerate(pieces)for b in ps}
            assert actual==expect and P==choose(h+1,2)+1 and W==h*h-h+2
            assert all(b[1]==h+4 for b in betti.values())
    windows=[]
    for d in [1,3]:
        m=d*u+2;gens=[m+d*a for a in [0,*offsets,u]];N=2*u
        max_s=(N+1)*max(gens);orders=[-1]*(max_s+1);orders[0]=0
        for s in range(1,max_s+1):
            options=[orders[s-g]+1 for g in gens if s>=g and orders[s-g]>=0]
            if options:orders[s]=max(options)
        PG=sum(orders[n*m+d*b]==n for n,ps in enumerate(pieces)for b in ps)
        points=[];sums={0}
        for n in range(N+1):
            for b in sums:
                s=n*m+d*b
                if orders[s]==n and orders[s+m]>n+1 and orders[s+m+d*u]>n+1:points.append((n,b,s))
            sums={b+a for b in sums for a in [0,*offsets,u]}
        rr=len(points)
        assert PG<=P and rr<=W-u and rr<=u*max(height-2,0)
        windows.append(dict(m=m,d=d,PC=P,PG=PG,R_observed_through_degree=N,R_observed=rr,socle_points=points))
    return dict(u=u,a=offsets,P=P,W=W,Hx=height,QC_Betti=betti,actual_socle_windows=windows)
start=time.monotonic();cases=[]
for u in range(4,11):
    for a in combinations(range(1,u),3):
        g=u
        for x in a:g=gcd(g,x)
        if g==1:cases.append(profile(a,u))
for u,a in [(12,(1,6,7)),(14,(2,7,9)),(16,(3,8,11))]:cases.append(profile(a,u))
positive=[dict(u=c['u'],a=c['a'],**w)for c in cases for w in c['actual_socle_windows']if w['R_observed']>0]
nontrivial_kernel=[dict(u=c['u'],a=c['a'],**w)for c in cases for w in c['actual_socle_windows']if w['PG']<w['PC']]
assert positive and nontrivial_kernel
out=dict(status='PASS_INDEPENDENT_FINITE_CORE_MODELS',scope='finite QC Koszul ranks; bounded-window actual socle observations, not full actual Betti or universal proof',profiles=len(cases),characteristics=[0,2,3],matrix_profiles=3*len(cases),actual_socle_windows=2*len(cases),positive_socle_windows=len(positive),PC_ne_PG_windows=len(nontrivial_kernel),positive_examples=positive[:8],seconds=round(time.monotonic()-start,3),cases=cases)
if output is not None:
    output.parent.mkdir(parents=True,exist_ok=True)
    with output.open('x')as f:f.write(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:v for k,v in out.items()if k!='cases'},indent=2))
