"""Independent exact checks. Finite samples are diagnostics, not a universal proof."""
from itertools import combinations
if not __debug__:
    raise RuntimeError('Run without -O: exact checks require assertions')

from fractions import Fraction
import random, json
from pathlib import Path

def mons(r, n):
    if n < 0: return []
    if r == 1: return [(n,)]
    return [(a,)+m for a in range(n+1) for m in mons(r-1,n-a)]

def rank(rows,p):
    if not rows: return 0
    a=[x[:] for x in rows]; nr=len(a); nc=len(a[0]); j=0
    for col in range(nc):
        pivot=next((i for i in range(j,nr) if a[i][col]%p),None)
        if pivot is None: continue
        a[j],a[pivot]=a[pivot],a[j]
        u=pow(a[j][col]%p,-1,p); a[j]=[(v*u)%p for v in a[j]]
        for i in range(j+1,nr):
            u=a[i][col]%p
            if u: a[i]=[(v-u*w)%p for v,w in zip(a[i],a[j])]
        j+=1
        if j==nr: break
    return j

def rref(rows,nc,p):
    a=[x[:] for x in rows]; j=0; piv=[]
    for col in range(nc):
        pivot=next((i for i in range(j,len(a)) if a[i][col]%p),None)
        if pivot is None: continue
        a[j],a[pivot]=a[pivot],a[j]
        u=pow(a[j][col]%p,-1,p); a[j]=[(v*u)%p for v in a[j]]
        for i in range(len(a)):
            if i==j: continue
            u=a[i][col]%p
            if u: a[i]=[(v-u*w)%p for v,w in zip(a[i],a[j])]
        piv.append(col); j+=1
        if j==len(a): break
    return a[:j],piv

def module(r,q,D,relations,p):
    # Presentation P^q /(relations, m^D P^q), all generators degree zero.
    ambient=[[(c,m) for c in range(q) for m in mons(r,d)] for d in range(D)]
    inds=[{x:i for i,x in enumerate(b)} for b in ambient]
    data=[]
    for d,amb in enumerate(ambient):
        rel=[]
        for degree,g in relations:
            for mul in mons(r,d-degree):
                row=[0]*len(amb)
                for (c,m),coef in g.items():
                    target=(c,tuple(x+y for x,y in zip(m,mul)))
                    row[inds[d][target]]=(row[inds[d][target]]+coef)%p
                rel.append(row)
        rr,piv=rref(rel,len(amb),p)
        free=[i for i in range(len(amb)) if i not in piv]
        data.append((rr,piv,free))
    mult={}
    for d in range(D-1):
        rr,piv,targetfree=data[d+1]
        for v in range(r):
            matrix=[]
            for f in data[d][2]:
                c,m=ambient[d][f]; n=list(m); n[v]+=1
                vec=[0]*len(ambient[d+1]); vec[inds[d+1][(c,tuple(n))]]=1
                for row,pivot in zip(rr,piv):
                    u=vec[pivot]
                    if u: vec=[(a-u*b)%p for a,b in zip(vec,row)]
                matrix.append([vec[i] for i in targetfree])
            mult[d,v]=matrix
    h=[len(x[2]) for x in data]
    ranks={}; bounds=0
    for i in range(1,r+1):
        sourcewedges=list(combinations(range(r),i)); targetwedges=list(combinations(range(r),i-1))
        wi={w:a for a,w in enumerate(targetwedges)}
        for t in range(1,D):
            rows=[[0]*(h[t-1]*len(sourcewedges)) for _ in range(h[t]*len(targetwedges))]
            for widx,w in enumerate(sourcewedges):
                for f in range(h[t-1]):
                    col=widx*h[t-1]+f
                    for a,v in enumerate(w):
                        targetw=w[:a]+w[a+1:]; offset=wi[targetw]*h[t]
                        for out,c in enumerate(mult[t-1,v][f]):
                            rows[offset+out][col]=(rows[offset+out][col]+(-1)**a*c)%p
            value=rank(rows,p); ranks[i,t]=value
            if i>=2:
                j=i-1
                import math
                target=Fraction(math.comb(r-1,j)*t*h[t],t+j)
                assert value>=target,(r,q,D,p,i,t,h,value,target)
                bounds+=1
    # All maps into degree zero or into degree >=D are zero.
    betti=[]
    for i in range(r+1):
        import math
        n=math.comb(r,i)*sum(h)
        betti.append(n-sum(ranks.get((i,t),0) for t in range(1,D))-sum(ranks.get((i+1,t),0) for t in range(1,D)))
    for j in range(1,r):
        c=sum((-1)**(j-i)*betti[i] for i in range(j+1))
        right=math.comb(r-1,j)*sum((Fraction(j,t+j)*ht for t,ht in enumerate(h)),Fraction())
        assert c<=right,(r,q,D,p,j,h,betti,c,right)
    return bounds,h,betti

def main():
    import argparse
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--out',type=Path,default=Path(__file__).resolve().parents[1]/'certificates/harmonic_summary.json')
    parser.add_argument('--full',action='store_true',help='Include all finite module cases in the output')
    args=parser.parse_args()
    rng=random.Random(340197); checks=0; cases=[]
    for r in (2,3,4):
        for q in (1,2,3):
            for D in (2,3,4):
                for sample in range(3):
                    rel=[]
                    for d in range(1,D):
                        amb=[(c,m) for c in range(q) for m in mons(r,d)]
                        for z in range(rng.randrange(1,min(5,len(amb))+1)):
                            g={x:rng.randrange(-2,3) for x in amb}
                            rel.append((d,{x:c for x,c in g.items() if c}))
                    for p in (2,3,101):
                        count,h,b=module(r,q,D,rel,p); checks+=count
                        cases.append(dict(r=r,q=q,D=D,sample=sample,p=p,h=h,betti=b))
    output=dict(status='PASS_FINITE_DIAGNOSTICS',module_cases=len(cases),degreewise_rank_checks=checks,primes=[2,3,101],caution='Finite diagnostics; universal proof is HUMAN_PROOF_REDUCED.md section 6')
    if args.full: output['cases']=cases
    args.out.parent.mkdir(parents=True,exist_ok=True)
    args.out.write_text(json.dumps(output,indent=2)+'\n')
    print(json.dumps({k:v for k,v in output.items() if k!='cases'}))

if __name__=='__main__': main()

