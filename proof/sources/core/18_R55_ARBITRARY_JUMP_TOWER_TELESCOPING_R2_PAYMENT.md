# R55: arbitrary-jump tower telescoping pays the first r2 rank budget

## Universal r2 statement

Let G be an actual numerical semigroup tangent cone, multiplicity m,
actual embedding dimension e>=3, delta=m-e. Let x=[m], and let y,z be
two distinct actual non-x variables such that

    A=G/xG is generated in degrees0,1 over P=k[y,z].

Equivalently the actual quotient A/(y,z)A is square-zero. Let
N be the non-Apéry-head ideal, Q=A/N, nu=reg(Q), and q_j=dim Q_j.
Thus sum_(j=2)^nu q_j=delta. Let

    a=dim ann_A(y,z),  u=dim T/(y,z)T,  T=(0:_G x).

**Theorem.** Uniformly over every field, for delta>=1,

    a+u <= e-1+3delta+delta(m+1)/4.                    (1)

Consequently the actual first generic relative rank c1=a+u-rho satisfies

    c1 <= (e-1)(delta+1)+C(delta+1,2)=R1                (2)

whenever `3e+delta>=15`. In particular this holds for every e>=4,
delta>=3. The already proved delta<=2 rank-payment theorem and the
accepted small-embedding-dimension cases cover the remaining numerical
P14 cases. Together with the universal top-rank theorem, this closes
the r2 budget for all sources in the stated large-parameter chamber.
It does not assert that every source admits an actual hitting pair.
The small cases are closed explicitly at the end, yielding the universal
r2 payment for every such cut.

## 1. Finite two-variable generator-socle cancellation

For any short exact sequence of finite graded P-modules

    0 -> K -> M -> L -> 0,

write u(X)=dim X/(y,z)X and v(X)=dim ann_X(y,z). Then

    u(K)<=u(M)+v(L).                                  (3)

**Proof.** The end of the Koszul long exact sequence gives

    u(K)=u(M)-u(L)+lambda,

where lambda is the rank of H1(y,z;L)->H0(y,z;K). Since L is finite,
the two-variable Koszul Euler identity is dim H1(L)=u(L)+v(L).
Therefore lambda<=u(L)+v(L), proving (3). This cancels the u(L) term
in the inequality; discarding the negative u(L) before applying Euler
would lose precisely the needed intermediate-layer resource. QED.

## 2. An actual quotient tower for every jump

The opposite-filtration theorem gives actual ideals

    F_d=N_(jump<=d),  F_1=0,  F_nu=N.

All terminal jumps lie between2 andnu. Put

    A^(d)=A/F_(d-1),   K_d=F_d/F_(d-1)  (2<=d<=nu).

K_d is an ideal in A^(d), supported in degrees>=d+1, because a terminal
has positive order. The quotient A^(d) agrees with Q through degree d:
all remaining non-Apéry heads have jump>=d and degree>=d+1. All these
quotients remain generated over P in degrees0,1 and have Hilbert
functions bounded by the actual h_j(A).

Define the actual truncation modules

    M_d=A^(d)_(>=d+1),
    L_d=A^(d+1)_(>=d+1).

The quotient map gives an exact sequence

    0 -> K_d -> M_d -> L_d -> 0.                       (4)

Since A^(d) is generated over P in degrees0,1, M_d is generated in
its first degree d+1. Moreover A^(d)_d=Q_d, so

    u(M_d)=dim A^(d)_(d+1)<=2q_d.                     (5)

For d=nu, L_d=Q_(>=nu+1)=0. For d<nu, the relative socle of L_d
is exactly the relative socle of A^(d+1) in degrees>=d+1. The latter
quotient has degree-(d+1) mass q_(d+1).

## 3. One allocation of every Apéry degree

Use the established Ferrers lemma from the cubic-Apéry proof: for a
finite P-module generated in degrees0,1, with numerical Hilbert bound
h_j<=m-j and degree-D mass q, its relative socle in degrees>=D has
size at most

    F(q)=q+floor(q/2)*floor((m+1)/2)
        <=q+q(m+1)/4.                                (6)

For completeness, choose a monomial initial submodule of a presentation
of the finite P-module with basis shifts0,1. A row-reduced actual socle
basis has distinct leading normal monomials, and their y,z multiples
are in the initial submodule; thus actual socles inject into monomial
socles in each degree. The initial module is a sum of shifted cyclic
Ferrers order ideals. A component with zero degree-D mass has no
socle in degree>=D. If that mass is one, any higher standard word
must have that one degree-D divisor; its higher standards form at most
one pure chain (or a single mixed word without extension), so it has at
most one such socle. Hence components with one or two socles can charge
them to distinct degree-D standards, whereas a component with at least
three such socles consumes at least two degree-D standards.

If a component has r>=3 socles, list them in increasing y exponent and
decreasing z exponent. Their exponents force all r diagonal monomials
`y^(i-1)z^(r-i)` to be standard. Their actual degree is r-1 or r,
according to the basis shift, and is at least2. The numerical bound
h_j<=m-j therefore gives r<=floor((m+1)/2). There are at most
floor(q/2) such large components; the remaining small ones contribute
at most q. This proves(6), including socles of degree exactly D.

It applies to every A^(d), since each is a quotient of the genuine A.
Equations(3)--(6) give

    u(K_d)<=2q_d+F(q_(d+1)) (d<nu),
    u(K_nu)<=2q_nu.                                   (7)

The opposite filtration of T has the same common strata K_d with
standard degree shifts. Generator spaces are subadditive in every
short exact sequence. Consequently

    u(T)<=sum_(d=2)^nu u(K_d)
         <=2delta+sum_(j=3)^nu F(q_j).                 (8)

The degree-zero coordinate1 is not a relative socle; the degree-one
relative socle has dimension at most e-1. Applying(6) to A in degree2,
where A2=Q2, gives

    a<=e-1+F(q2).                                     (9)

Add(8),(9) and allocate every q_j exactly once:

    a+u(T)<=e-1+2delta+sum_(j=2)^nu F(q_j)
           <=e-1+3delta+delta(m+1)/4.

This proves(1) for arbitrary nu. No bound on nu by a small constant,
no globally commuting successor map, no split extension, no vanishing
induced correction, and no zero outside-variable action was assumed.

Finally direct subtraction from R1 gives

    R1-[e-1+3delta+delta(m+1)/4]
      =delta(3e+delta-15)/4.

This proves(2). The argument pays a+u itself, so the actual nonnegative
rho can only improve the comparison. The separate universal top-rank
payment supplies c2; no statement about larger cuts follows merely
from this r2 calculation. QED.

## Exact scope

The new step is the truncation sequence(4) and the cancellation(3),
which handle intermediate jump-layer births. The Ferrers lemma,
canonical N/Q ideal, opposite filtration, universal terminal-jump
bound, actual numerical h_j<=m-j, and exact r2 formula are already
proved within R55. All finite-module arguments are characteristic
independent. The P14 conclusion uses the source's actual ordinary
interval target through the accepted r2 rank comparison.

The theorem closes an r2 payment obligation; sources whose smallest
actual quadratic hitting set has size>=3 still require a different
argument. No unrestricted ordinary P14 closure is asserted.


## Complete small-case assembly: universal r2 payment

The conditions `e>=4,delta>=3` and `e=3,delta>=6` are paid by the
proved main inequality. The independent R55 delta<=2 theorem covers
those defects for every e. For e3 and delta3,4,5, use the proved R55
microinvariant torsion cap

    t<=sum_(j=1)^(m-1) min(delta,floor((j-1)/2)).

It gives respectively t<=4,6,9 at m6,7,8. Since the unit of A is not
killed by y,z, `a<=length(A)-1=m+t-1`, while `u(T)<=t`. Thus

| e | delta | m | t cap | a+u cap | R1 |
|---:|---:|---:|---:|---:|---:|
|3|3|6|4|13|14|
|3|4|7|6|18|20|
|3|5|8|9|25|27|

All remaining cases are paid. Therefore the first actual r2 rank
budget is universal for every actual hitting pair. Combining this
with `UNIVERSAL_R2_TOP_RANK_PAYMENT.md` proves both generic-rank
budgets over every field. For an actual ordinary target, the accepted
rank comparison proves all P14 rows. The flag
`R_TWO_PAYMENT_CLOSED=true` refers exactly to this hitting-pair
statement; it does not close sources requiring three or more actual
steering variables.
