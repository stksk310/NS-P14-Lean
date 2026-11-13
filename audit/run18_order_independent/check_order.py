#!/usr/bin/env python3
"""Independent audit of Run18 ORDER, not an implementation or universal Lean proof.

No project checker is imported or executed. No pre-existing evidence is written.
stdout only; exact integers/Fractions and symbolic polynomial identities.
"""
from collections import Counter
from fractions import Fraction as F
from itertools import combinations
from math import comb, gcd
import json
import sympy as sp

counts = Counter()
def C(n, k):
    return comb(n, k) if 0 <= k <= n else 0
def require(ok, label):
    assert ok, label
    counts[label] += 1
def identity(lhs, rhs, label):
    require(sp.cancel(lhs-rhs) == 0, label)
def B(u, a, s):
    return u + sum(max(0, u-a-s*j) for j in range(u+1))
def T(e, i, u):
    return F(i*C(u,i+1), C(e,i)) + F(u*i,e) + F((e-i)*(e-i-1),e*(i+1))

z, v, x, k, b = sp.symbols('z v x k b', nonnegative=True)
ee, aa, ss = sp.symbols('e a s', positive=True)
uu = aa+ss*k+b
bb = uu + ss*k*(k+1)/2 + (k+1)*b
identity(2*aa*(uu**2/aa-bb), ss*(2*ss-aa)*k**2+aa*ss*k+2*(2*ss-aa)*k*b+2*b**2, 'B_quadratic_identity')
for e, wanted in [(6,z*z/24+43*z/24+sp.Rational(1,2)),(7,2*z+1),
                   (8,3*z*z/32+63*z/16+sp.Rational(211,32)),
                   (9,z*z/16+17*z/4+sp.Rational(29,4))]:
    u=2*e-2+z; a=e-1; s=e//2; delta=u-a
    bs=u+delta**2/(2*s)+delta/2+sp.Rational(s*s//4,2*s)
    upper=sp.Rational(e+5,4)*bs-u+sp.Rational((e-1)*e*(e+1),24)
    identity(u*(u-1)/2+1-upper,wanted,'sparse_first_small_symbolic')
u=2*ee-2+z
identity(u*(u-1)/2+1-((ee+3)*u*u/(3*(ee-1))-u+ee*(ee-1)/6),
         (ee-1)*(ee-10)/2+1+(4*ee-33)*z/6+(ee-9)*z*z/(6*(ee-1)), 'sparse_first_large_symbolic')
e=8+v; u=2*e-2+z
identity(2*u*u-(3*e+6)*u+6*e-2,2*v*v+5*v*z+16*v+2*z*z+26*z+18,'sparse_second_large_symbolic')
identity(2*(12+z)**2-27*(12+z)+40,2*z*z+21*z+4,'sparse_second_seven_symbolic')
identity(x*(x-1)*(x-2)/3-(3*x*x-5*x-10),(x-10)*(x-3)*(x+1)/3,'sparse_second_six_symbolic')
t=4+z; q=t+v
identity(5*t*t-17*t-6+6*(t-1)*(q-t),5*z*z+23*z+6+6*z*v+18*v,'dense_positive_symbolic')
identity(x*(x-1)*(x-2)/3-(9*x*x/4-4*x),x*(4*x-7)*(x-8)/12,'five_second_symbolic')
for r in range(3):
    u=3*x+r
    pol=[(3*x*x+x+2)/2,(3*x*x+3*x+2)/2,(3*x*x+5*x+4)/2][r]
    want=[(3*x*x+x-26)/4,(3*x*x+3*x-22)/4,(3*x*x+5*x-24)/4][r]
    identity(u*(u-1)/2+1-(5*pol/2-u+5),want,'five_first_symbolic')

for e in range(6,41):
    a=e-1; s=e//2
    for u in range(2*e-2,2*e+61):
        delta=u-a; kk,rem=divmod(delta,s); bound=B(u,a,s)
        exact=u+F(delta*delta,2*s)+F(delta,2)+F(rem*(s-rem),2*s)
        star=u+F(delta*delta,2*s)+F(delta,2)+F(s*s//4,2*s)
        require(bound==exact<=star and bound<=F(u*u,a),'sparse_volume')
        upper=(F(e+5,4)*star-u+F((e-1)*e*(e+1),24)) if e<10 else (F(e+3,3)*F(u*u,a)-u+F(e*(e-1),6))
        require(upper<C(u,2)+1,'sparse_first_payment')
        for i in range(2,e+1):
            U=bound*C(e,i)-u*C(e-1,i-1)-C(e-1,i+1)
            require(T(e,i,e)==e-1+F(i,e),'sparse_T_base')
            require(T(e,i,u+1)-T(e,i,u)==F(i*C(u,i),C(e,i))+F(i,e),'sparse_T_increment')
            require(T(e,i,u)>=T(e,2,u)>=bound and i*C(u,i+1)>=U,'sparse_all_higher_payment')
for q in range(4,41):
    for t in range(2,q+1):
        R=0 if t==2 else t
        K=2 if t==2 else (4 if t==3 else F(2*t*(t-1),3))
        for i in range(1,q+3):
            A=C(q-1,i-1); CC=C(q,i-1); BB=C(q+1,i-1)
            diff=i*(C(q+t+1,i+1)-C(q+1,i+1))-(q+1+2*t)*CC-R*BB-K*A
            lower=(q-3)*CC+i*BB-2*A if t==2 else ((2*q-4)*CC+(3*i-3)*BB-4*A if t==3 else (F(5*t*t-17*t-6,6)+(t-1)*(q-t))*CC)
            require(diff>=lower>=0,'dense_payment')
for u in range(8,301):
    j,r=divmod(u,3); bb=B(u,4,3)
    require(bb==[F(3*j*j+j+2,2),F(3*j*j+3*j+2,2),F(3*j*j+5*j+4,2)][r],'five_B3')
    upper=F(5*bb,2)-u+5
    require(upper.numerator//upper.denominator<=C(u,2)+1,'five_first_floor')
    require(bb<=F(u*u,4),'five_resource')
    for row,upper in [(2,F(9*u*u,4)-4*u),(3,F(5*u*u,2)),(4,F(5*u*u,4)),(5,F(u*u,4))]:
        require(upper<=row*C(u,row+1),'five_high_payment')
for h in range(4,101):
    P=C(h+1,2)+1; W=h*h-h+2; u=2*h
    require(C(u,2)+1-(P+h+4+W-u)==F(h*h+h-12,2)>=0,'antipodal_first')
for u,P,R,want in [(6,8,0,[46,60,39,11]),(7,10,3,[77,126,119,56])]:
    target=[i*C(u,i+1)+min(C(u,i-1),C(u,i)) for i in range(2,6)]
    require(target==want and all(a<=b for a,b in zip([5*P+4*R,4*P+6*R-1,P+4*R,R],target)),'five_small_table')

def rank(matrix,p):
    # Independent forward Gaussian elimination, over Q for p=0 and F_p otherwise.
    if not matrix:return 0
    M=[[F(a) if not p else a%p for a in row]for row in matrix]
    pivot=0
    for col in range(len(M[0])):
        rr=next((r for r in range(pivot,len(M))if M[r][col]),None)
        if rr is None:continue
        M[pivot],M[rr]=M[rr],M[pivot]
        inv=1/M[pivot][col] if not p else pow(M[pivot][col],-1,p)
        for r in range(pivot+1,len(M)):
            factor=M[r][col]*inv
            if p:factor%=p
            if factor:
                M[r]=[(a-factor*b)%p if p else a-factor*b for a,b in zip(M[r],M[pivot])]
        pivot+=1
        if pivot==len(M):break
    return pivot
def core(a,u):
    sums=[{0}]; pieces=[{0}]
    for n in range(1,u+1):
        prev=sums[-1]
        sums.append({b+c for b in prev for c in [0,*a,u]})
        pieces.append(sums[-1]-prev-{b+u for b in prev})
    require(not pieces[u], 'core_cutoff_finite')
    return pieces
def differential(a,pieces,n,i):
    q=len(a); sw=list(combinations(range(q),i)); tw=list(combinations(range(q),i-1))
    src=[(b,J)for b in sorted(pieces[n])for J in sw]
    tgt=[(b,J)for b in sorted(pieces[n+1])for J in tw]; index={x:j for j,x in enumerate(tgt)}
    mat=[[0]*len(src) for _ in tgt]
    for c,(b,J)in enumerate(src):
        for j,vv in enumerate(J):
            dest=index.get((b+a[vv],J[:j]+J[j+1:]))
            if dest is not None:mat[dest][c]+=(-1)**j
    return mat
def betti(a,pieces,p):
    q=len(a); P=sum(map(len,pieces)); ranks=[0]
    for i in range(1,q+1):
        ranks.append(sum(rank(differential(a,pieces,n,i),p)for n in range(len(pieces)-1)))
    ranks.append(0)
    return [P*C(q,i)-ranks[i]-ranks[i+1]for i in range(q+1)]
for u in range(5,10):
    q=u-2
    for missing in range(1,u):
        a=[x for x in range(1,u)if x!=missing]; pieces=core(a,u)
        interior=1<missing<u-1
        require(pieces[2]==({missing,missing+u}if interior else ({u+1}if missing==1 else {u-1})) and not any(pieces[3:]),'edge_core_basis')
        for p in [0,2,3]:
            bs=betti(a,pieces,p)
            for i in range(1,q+3):
                bi=bs[i] if i<len(bs) else 0
                if interior:
                    r=missing-1; s=u-missing-1
                    rho=2*C(q,i-1)-C(s,i-1-r)-C(r,i-1-s)
                    require(rank(differential(a,pieces,1,i),p)==rho,'edge_signed_rank')
                    extra=C(s+1,i-r)+C(r+1,i-s)
                    require(bi==i*C(q+1,i+1)-2*C(q,i-1)+extra,'edge_QC_Betti')
                    require(extra<=min(C(q+2,i-1),C(q+2,i)),'edge_injection_bound')
                envelope=i*C(q+2,i+1)+min(C(q+2,i-1),C(q+2,i))
                require(bi+sum(map(len,pieces))*C(q,i-1)<=envelope,'edge_transfer_payment')
for q in range(3,6):
    for t in range(q+1):
        u=q+1+t
        for a in combinations(range(1,u),q):
            g=u
            for x in a:g=gcd(g,x)
            if g!=1:continue
            pieces=core(a,u); P=sum(map(len,pieces))
            height=max(n-(offset+u-1)//u for n,ps in enumerate(pieces)for offset in ps)
            require(height<=t and not any(pieces[t+2:]),'dense_actual_height_length')
            reach={0}; dist={0:0}
            for n in range(1,3):
                reach={(x+y)%u for x in reach for y in [0,*a]}
                for r in reach:dist.setdefault(r,n)
            require(len(dist)==u and 1+sum(dist.values())==q+1+2*t and P<=q+1+2*t,'dense_actual_volume')
for h in range(4,10):
    for t in range(1,h):
        if gcd(t,h)!=1:continue
        u=2*h; a=[t,h,t+h]; pieces=core(a,u)
        expected=[{0}]+[{t,h,t+h}]+[{n*t+h*j for j in range(n+1)}for n in range(2,h)]
        expected += [set()]*(len(pieces)-len(expected))
        require(pieces==expected and sum(map(len,pieces))==C(h+1,2)+1,'antipodal_actual_core')
        for p in [0,2,3]:
            require(betti(a,pieces,p)[1]==h+4,'antipodal_actual_betti')
        reach={0}; distance={0:0}
        for n in range(1,u):
            reach={(x+y)%u for x in reach for y in [0,*a]}
            for r in reach:distance.setdefault(r,n)
        require(len(distance)==u and 1+sum(distance.values())==h*h-h+2,'antipodal_actual_volume')
print(json.dumps({'status':'PASS_ORDER_CHECKS_ONLY','scope':'instruction arithmetic and finite independent integer-core/Koszul models; not Lean closure', 'counts':dict(counts),'characteristics':[0,2,3]},indent=2))
