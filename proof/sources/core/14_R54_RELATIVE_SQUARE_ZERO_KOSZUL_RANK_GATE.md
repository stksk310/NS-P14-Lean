# R54: relative square-zero Koszul transport without a splitting assumption

## Universal relative bound

Let G be an actual numerical semigroup tangent cone, with genuine
variables x=[m], y_1,...,y_(e-1). Let E be r>=1 of the actual non-x
variables such that

    Q=G/(x,E)G

is square-zero in positive degree. The actual linear coordinates are
independent, so Q has embedding dimension f=e-r-1 and length f+1=e-r.
The quadratic-head hitting construction supplies such an E with r<=delta,
but the present theorem only requires the stated square-zero quotient.

Put P=k[x,E], the polynomial ring on these r+1 declared variables,
and let

    b_h=dim_k Tor_h^P(G,k),   0<=h<=r+1.

Then, over EVERY field and every row,

    beta_i^S(G) <= i*binom(f+1,i+1)
                    +sum_(h=1)^(r+1) b_h*binom(f,i-h),   i>=1.  (1)

Here S is the actual polynomial ring on all e source variables. No
A-module splitting, commuting division, universal primitive pivot,
characteristic-zero degeneration, or higher-rank equality is assumed.

### Proof

The variables P_+ annihilate H_h(K_P(G)) up to the standard explicit
Koszul nullhomotopies. These homology modules are finite dimensional
because x is a parameter and G/(x)G has finite length. Partition the
actual Koszul complex as the bicomplex

    K_Z(K_P(G)),

where Z is the set of f remaining actual variables. First taking
P-homology and then Z-homology gives the convergent degreewise bounded
spectral sequence

    E^2_(j,h)=Tor_j^(k[Z])(H_h(K_P(G)),k)
       ==> Tor_(j+h)^S(G,k).

The h=0 module is exactly Q, with its actual square-zero Z action.
Its Betti totals are beta_0(Q)=1 and
beta_j(Q)=j*binom(f+1,j+1) for j>=1, integrally as for the ordinary
square-zero algebra. For h>=1 its Z-Koszul chain in degree j has
dimension b_h*binom(f,j), hence its homology is at most that number.
Subsequent spectral differentials only decrease dimensions. Summing
in total degree i proves (1). This is an upper bound, not an assertion
that the spectral sequence splits or degenerates. QED.

## Generic relative syzygy ranks and a sharper form

The finite-dimensional quotient Q shows by graded Nakayama that G is a
finitely generated graded P-module with exactly b_0=f+1=e-r minimal
P-generators, one constant and f actual linears. Since dim G=1<r+1,
it has rank zero over Frac(P). Tensoring its minimal P-resolution with
Frac(P) gives an exact complex of vector spaces ending in zero. Thus

    c_j=sum_(h=0)^j (-1)^(j-h)b_h,    0<=j<=r,

are NONNEGATIVE integers: c_j is the generic rank of the (j+1)st
resolution differential. Also c_0=b_0 and

    sum_(h=0)^(r+1)b_h u^h=(1+u)sum_(j=0)^r c_j u^j.

Substitute this identity in (1) and use the ordinary polynomial identity
T_(v+1)-T_v=v*u*(1+u)^(v-1), where

    T_v=1+sum_(i>=1)i*binom(v,i+1)u^i.

The resulting coefficientwise actual bound is

    P_G^S(u) <= T_(e-r+1)(u)
                 +(1+u)^(e-r)sum_(j=1)^r c_j u^j.         (2)

The polynomial T_(e-r+1) is only an algebraic comparison budget; it is
not asserted to be an actual intermediate semigroup target.

## An explicit ordinary-target rank-vector certificate

Suppose the ACTUAL interval completion of G is ordinary of multiplicity
m=e+delta. Telescoping its exact target polynomial gives

    T_m-T_(e-r+1)
      =u*(1+u)^(e-r)
          sum_(l=0)^(delta+r-2)(e-r+1+l)(1+u)^l.

Consequently the sufficient all-row rank-vector inequalities are

    c_j <=R_j(e,delta,r),        1<=j<=r,
    R_j=(e-r+j)*binom(delta+r-1,j)
                      +j*binom(delta+r-1,j+1).            (3)

The displayed R_j is exact: sum_l l*binom(l,j-1) is evaluated using
l*binom(l,j-1)=(j-1)*binom(l,j-1)+j*binom(l,j).
Equations (2)-(3) imply P14 with the actual ordinary target. A weaker
necessary-for-this-upper-bound rowwise test is obtained by comparing
(2) directly with T_m; separate inequalities (3) are convenient sufficient
conditions and are not claimed necessary for P14.

For r=1, c_1=b_2=dim ann_G(x,E), and (3) is exactly

    c_1<=delta e+binom(delta,2).

For r=2,

    c_1=b_1-(e-2)=b_2-b_3,
    c_2=b_3=dim ann_G(x,E),

and the explicit sufficient budgets become

    c_1<=Delta+e-1,
    c_2<=e*binom(delta+1,2)+2*binom(delta+1,3).

The second budget is substantially larger than charging the common
annihilator by the same scalar Delta in every row. These are actual
P-relative homology ranks, which may depend on the field. The theorem
holds separately over every field; an all-field application must prove
uniform inequalities or a uniform integral homology basis. Rational
sample ranks may not be substituted for that requirement.

## Remaining universal gap

Quadratic-head compression gives r<=delta and makes b_0=e-r explicit,
with multiplicity deviation m-b_0=delta+r<=2delta. It does NOT bound
the positive generic syzygy ranks c_j by (3). Controlling those ranks,
or the actual later Z actions rather than their chain dimensions, is
the remaining mechanism needed for a universal ordinary-target proof.
The present theorem is a rigorous conditional rank certificate, not
GLOBAL_CLOSED and not an assumed generalization of commuting division.
