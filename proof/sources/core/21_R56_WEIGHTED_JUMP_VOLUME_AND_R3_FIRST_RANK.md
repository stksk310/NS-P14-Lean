# R56: exact weighted jump volume and the three-steering first rank

## Statement

Let `Gamma=<m=g_1<...<g_e>` be a genuine numerical semigroup with its
actual minimal generating set, and let `G` be its tangent cone over an
arbitrary field. Put `delta=m-e`, `x=[m]`, `A=G/xG`, and
`T=(0:_G x)`. Let `E={y,z,w}` be three distinct actual non-x variables
such that `A/EA` is square-zero. Thus `e>=4`, and `A` is generated in
degrees zero and one over `P=k[E]`.

Retain the actual non-Apery-head ideal `N`, its numerical Apery
quotient `Q=A/N`, and the opposite-jump tower from R55. Let

    F_d=N_(jump<=d),  U_j=A/F_(j-1),
    nu=reg(Q),       X_j=(U_j)_(>=j)  (2<=j<=nu).

The new source resource is the **exact identity**

    S := sum_(j=2)^nu length(X_j)
       = sum_(r != 0 mod m) (L_r-1),                         (1)

where `L_r` is the actual blow-up microinvariant specified below.
Consequently

    S <= delta(2e+delta-3)/2.                                (2)

For every integer `R>=1`, the first actual generic relative rank for
the four-variable cut `(x,E)` satisfies

    c_1(G) <= 2e-3+2delta+delta R^2+3 S/R.                   (3)

In particular its required budget

    R_1=(e-2)(delta+2)+C(delta+2,2)

is paid whenever

    delta=0, or 2e+delta>=133.                               (4)

The nonzero-defect part of (4) follows by taking `R=5`. All assertions
hold over every field. The statement does not claim that the first
rank budget is paid in the remaining finite parameter region merely
from this estimate. It also does not assert that every source admits
an actual hitting triple.

## 1. Numerical definitions and the terminal excess identity

For each residue `r mod m`, let `w_r` be its numerical Apery element,
let `s_r=ord_Gamma(w_r)`, let `d_r` be the least sum of positive
offsets `g_i-m` in that residue, and let `l_r` be the shortest word
length achieving `d_r`. Set

    L_r=(w_r-d_r)/m.

For `r!=0`, the already established numerical inequalities are

    1 <= s_r <= L_r <= l_r,
    L_r <= delta+1.                                         (5)

The last inequality is precisely the classical microinvariant input
used in R55, with its finite-field extension argument. We use no
stronger interpretation of it.

Write `a_r(q)=ord_Gamma(w_r+qm)` and `q_r=l_r-L_r`. The least-offset
argument gives

    a_r(q)=L_r+q  for q>=q_r.

Before this stable range, summing the excess in the order increments
gives the exact identity

    sum_(q=0)^(q_r-1) [a_r(q+1)-a_r(q)-1] = L_r-s_r.        (6)

A summand is zero precisely on a live x-arrow. On a dead x-arrow its
source is an actual finite x-string terminal `tau`, and the summand
is `d(tau)-1`, where

    d(tau)=ord_Gamma(tau+m)-ord_Gamma(tau).

There are no later dead x-arrows. Hence (6), summed over all nonzero
residues, proves

    sum_(actual terminals tau) [d(tau)-1]
       = sum_(r!=0) (L_r-s_r).                              (7)

This is a weighted jump identity, rather than the older bound on the
number of terminals. Replacing the left side by `delta*t` discards
the source resource needed here.

## 2. Count the tower volume exactly

The actual quotient `U_j` has a coordinate basis consisting of all
numerical Apery coordinates and those non-Apery successor heads whose
terminal jump is at least `j`.

An Apery coordinate of standard degree `n>=2` lies in `X_j` exactly
for `2<=j<=n`, so it contributes `n-1` to `S`. The total contribution
of these coordinates is

    sum_(n>=2) (n-1) dim Q_n = sum_(r!=0) (s_r-1).          (8)

For a terminal `tau` of jump `d`, its successor head `tau+m` survives
in `U_j` exactly for `j<=d`. Its degree is
`ord(tau)+d>=d+1`, so it automatically belongs to the truncation
`(U_j)_(>=j)` whenever it survives. It therefore contributes exactly
`d-1` to `S`. The universal jump bound `2<=d<=nu` ensures that all
these occurrences lie in the displayed finite sum defining `S`.
Thus its total non-Apery contribution is the left side of (7).

Adding (7) and (8) proves (1) with no filtration splitting and no
identification of `N` and `T` as whole modules.

Arrange the shortest least-offset lengths in nondecreasing order as
`l_(0),...,l_(m-1)`. The shortest-path prefix argument gives
`l_(j)<=j`: each prefix is again an optimal shortest offset word,
and its prefix residues are distinct. By (5),

    L_r-1 <= min(delta,l_r-1)  for r!=0.

The zero residue supplies the length-zero word. The monotonicity of
`min(delta,j-1)` on positive indices therefore gives

    S <= sum_(j=1)^(m-1) min(delta,j-1)
       = delta(m-1)-delta(delta+1)/2
       = delta(2e+delta-3)/2.

Here `m=e+delta` and `e>=4` guarantee that the sum reaches its
constant plateau. This proves (2), including `delta=0`.

## 3. Finite-module rank and border ingredients

For a finite P-module `M`, write

    b_i(M)=dim Tor_i^P(M,k),
    c_j(M)=sum_(i=0)^j (-1)^(j-i)b_i(M).

Thus `c_0(M)=mu(M)` and `c_1(M)=b_1(M)-mu(M)`. For an exact sequence
`0->K->M->L->0`, the actual Tor long exact sequence gives

    c_j(M)<=c_j(K)+c_j(L),
    mu(K)<=mu(M)+c_1(L).                                  (9)

Both statements retain the actual connecting ranks and hold over the
given field.

We also need the following elementary three-variable colength bound.
If `M` is finite, generated by `q` elements all in one degree, and
has length `ell`, then for every integer `R>=1`,

    c_1(M)<=q(R^2-1)+3ell/R.                              (10)

To prove it, take a homogeneous initial submodule of the kernel of a
minimal presentation `P(-a)^q -> M`. The initial quotient is a direct
sum of `q` shifted Artin monomial quotients `P/I_i`, with total
colength `ell`. Its first Betti number dominates that of `M`; this
also follows directly by lifting a Groebner basis of the presentation
kernel. For an Artin monomial ideal `I` of colength `ell_i`, its
minimal generators with all exponents less than `R` number at most
`R^2`: projection dropping one fixed exponent is injective on this
antichain. Assign every other minimal generator to one variable in
which its exponent is at least `R`. Its `R` successive proper
divisors in that variable are standard. For a fixed assigned
variable these sets of divisors are disjoint, so at most
`floor(ell_i/R)` generators can be assigned to it. Hence

    mu(I)<=R^2+3floor(ell_i/R).

Subtract one from the generator number for each cyclic quotient and
sum. This proves (10). It applies over the original field, including
finite and positive-characteristic fields.

## 4. Apply the source tower

Write `q_j=dim Q_j`; then `sum_(j>=2)q_j=delta`. The quotient `U_j`
agrees with `Q` in degrees through `j`. Since every `U_j` is generated
over P in degrees zero and one, its tail `X_j` is generated in degree
`j`, and

    mu(X_j)=q_j.                                          (11)

Let `K_d=F_d/F_(d-1)` and `M_d=(U_d)_(>=d+1)`. The actual truncation
sequence is

    0 -> K_d -> M_d -> X_(d+1) -> 0                       (12)

for `d<nu`; for `d=nu` its last term is zero. Moreover
`mu(M_d)<=3q_d`. Apply (9), then the opposite-jump filtration of T:

    mu(T)<=sum_d mu(K_d)
          <=3delta+sum_(j=3)^nu c_1(X_j).                (13)

The low-degree quotient `A/A_(>=2)` is, as a P-module,

    P/(y,z,w)^2  direct_sum  k(-1)^(e-4).

Its first generic rank is `5+2(e-4)=2e-3`. Since
`A_(>=2)=X_2`, subadditivity in (9) gives

    c_1^P(A)<=2e-3+c_1(X_2).                              (14)

The x-first Koszul spectral sequence gives the exact identity

    c_1^(k[x,E])(G)=c_1^P(A)+mu_P(T)-rho_2,

where `rho_2>=0` is the actual induced differential rank
`H_2(E;A)->H_0(E;T)`. In particular, (13)-(14) imply

    c_1(G)<=2e-3+3delta+sum_(j=2)^nu c_1(X_j).

Use (10), (11), and the definition of `S` to obtain

    c_1(G)<=2e-3+3delta+delta(R^2-1)+3S/R,

which is (3). No assumption that `rho_2` vanishes was made.

## 5. Exact first-budget comparison

For `delta>0`, put `V=e+delta/2-3/2`. The exact budget identity is

    R_1-(2e-3+2delta)=delta(V-1).

Equation (2) says `S<=delta V`. With `R=5`, the extra term in (3)
is at most

    delta(25+3V/5).

It is at most `delta(V-1)` precisely when `V>=65`, or
`2e+delta>=133`. Thus (4) follows. If `delta=0`, then `Q` has no
nonlinear coordinates and `N=T=0`; (14) gives `c_1<=2e-3=R_1`.

The new proof ingredient is the weighted volume identity (1) and its
numerical estimate (2). The elementary Artin border estimate and the
actual generic-rank tower transfer were already present in R55;
their combination with (1) gives the new r3 first-rank chamber.

## Characteristic and scope

The numerical identity (1) is an integer equality on actual
coordinates. The bound `L_r<=delta+1` is exactly the accepted
classical microinvariant theorem; its application over finite fields
uses scalar extension, as in R55. Every subsequent Tor inequality is
valid over the chosen field with its actual ranks. Monomial initial
modules and the elementary border proof require no characteristic
zero hypothesis. The proof therefore does not rely on the separate
four-variable total-unimodularity theorem.

The rank conclusion is for actual hitting triples. Combining it with
other inherited source-payment theorems is a separate assembly step;
an inherited all-row P14 theorem alone is not a proof of the same
relative first-rank inequality in the uncovered small parameter
region.
