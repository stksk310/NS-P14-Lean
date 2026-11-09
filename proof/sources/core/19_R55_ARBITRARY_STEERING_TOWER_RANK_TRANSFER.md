# Beyond r2: exact arbitrary-steering transfer and universal top-rank payment

## 1. A finite-module generic-rank inequality

Let P be a polynomial ring on r variables over any field. For a finite
P-module X put b_j(X)=dim Tor_j^P(X,k) and
c_j(X)=sum_(i=0)^j(-1)^(j-i)b_i(X). All identities and inequalities below use0<=j<=r-1. These are generic syzygy ranks,
nonnegative for0<=j<=r-1; put c_r=0. For an actual short exact sequence
0->K->M->L->0, let lambda_j be the actual connecting Tor_j(L)->Tor_(j-1)(K)
rank. Exactness gives

    c_j(K)=c_j(M)-c_j(L)+lambda_(j+1)
           <=c_j(M)+c_(j+1)(L).                     (1)

Indeed lambda_(j+1)<=b_(j+1)(L)=c_j(L)+c_(j+1)(L).
Also c_j(M)=c_j(K)+c_j(L)-lambda_(j+1), proving subadditivity under
extensions. These are field-specific exact ranks; no splitting or
characteristic-zero replacement is involved.

## 2. Apply the actual jump tower for any hitting size r

For an actual r-variable hitting set E, all quotient algebras A^(d)
are generated in degrees0,1 over P=k[E]. Retain the actual modules
K_d,M_d,L_d from the universal r2 proof. Their sequence remains exact
for every r, and

    mu(M_d)=dim A^(d)_(d+1)<=r*q_d.

The opposite filtration of T has the same shifted strata K_d. Thus(1)
and generic-rank subadditivity give

    c_j(T)<=sum_d[c_j(M_d)+c_(j+1)(L_d)].             (2)

In particular

    mu(T)<=r*delta+sum_(d=2)^(nu-1)c_1(L_d).          (3)

For r2, c1(L)=soc(L), and the inclusive two-dimensional Ferrers estimate
allocates it once to q_(d+1), completing the payment. For r3,

    c1(L)=beta2(L)-beta3(L)=beta2(L)-soc(L).

This penultimate Koszul term is the exact new cost requiring control.
The four-active-variable TU theorem makes the actual r3 cut ranks
field-independent; it does not supply a bound on that cost. No
three-dimensional Ferrers or universal middle-rank payment is asserted.

The x-first two-row Koszul spectral sequence also gives EXACTLY, in
every r and field,

    c1^(k[x,E])(G)=c1^P(A)+mu_P(T)-rho,

where rho is the induced d2:H2(E;A)->H0(E;T) rank. Only this d2 can
change total homology degree1. Equations(1)--(3) retain the actual
source and identify a precise generalization target; they do not
bound its right side by R1 universally.

## 3. The top generic rank is paid for EVERY r>=2

For an actual (r+1)-variable cut (x,E) with |E|=r non-x steering variables, its top generic rank is

    c_r=b_(r+1)=dim ann_G(x,E)<=t.

Let R_r=e*C(delta+r-1,r)+r*C(delta+r-1,r+1) be the top R54 budget.
For delta0, the microinvariant bound gives t=0. For delta>=1 split:

- If e>=delta+2, the proved dense cap gives t<=delta(e-2). Since
  C(delta+r-1,r)>=delta, R_r>=delta*e>=t.
- If e<=delta+1, necessarily delta>=2 (r>=2 implies e>=3). Then
  m<=2delta+1, and the microinvariant sum bound gives
  t<=floor((m-2)^2/4)<=delta(delta-1). Moreover
  C(delta+r-1,r)>=C(delta+1,2), and
  R_r>=e*C(delta+1,2)>=3delta(delta+1)/2>t.

Therefore c_r<=R_r over every field, for every actual hitting size
r>=2. The argument does not depend on any characteristic rank equality.
For r3 this leaves c1,c2, not the top c3. For arbitrary r the remaining
middle ranks and the first rank still need a universal source payment.

## Final global scope

The exact arbitrary-r identities and the universal top budget are new
continuations AFTER r2 closure. They do not imply that every source has
an r2 cut. Genuine examples in this packet require3 or4 actual steering
variables; these particular examples are already paid by other gates.
The remaining actual ordinary obligation has minimum hitting size>=3
and is OPEN. No uncontrolled Euler truncation, Smith primitivity, or
nonflat generator-deletion monotonicity is used here.
