# R55: opposite jump filtrations of terminals and non-Apéry heads

## Universal structural theorem

Use the notation of `APERY_QUOTIENT_SOCLE_TORSION_FUSION.md`: B is an
arbitrary numerical semigroup tangent cone, x its actual multiplicity
variable, f its actual embedding dimension, S the polynomial ring on
the f-1 other actual variables, T=(0:_B x), and N the ideal of
non-Apéry heads in A=B/xB.

Let F be the numerical-coordinate basis of T, the finite x-string
terminals. For tau in F define its positive integer **jump**

    d(tau)=ord(tau+m)-ord(tau)>=2.

The basis bijection tau -> tau+m identifies F with the basis of N.
It is generally not a module map. The following theorem states exactly
what survives of that proposed identification.

**Theorem 1 (opposite filtrations, common strata).**

1. If multiplication by an actual non-x variable is live on T from tau
   to sigma, then d(sigma)>=d(tau).
2. If it is live on N from tau+m to sigma+m, then d(sigma)<=d(tau).
3. On an equal-jump pair, the two actions coincide under the basis
   bijection: either both are live or both are zero.
4. Consequently the descending filtration

       F_>=d T = span{tau: d(tau)>=d}

   and the ascending filtration

       E_<=d N = span{tau+m: d(tau)<=d}

   are S-submodule filtrations. If

       K_d=F_>=d T / F_>d T,

   then the corresponding associated-graded piece of N is K_d with
   its standard degrees increased by d, and its numerical weights
   increased by m. In particular, over every field,

       beta_i^S(T)<=sum_d beta_i^S(K_d),
       beta_i^S(N)<=sum_d beta_i^S(K_d).                 (1.1)

All assertions hold integrally on coordinate bases. They do not assert
that either filtered module splits.

**Proof.** For a live T-product by an atom b, commutativity gives
`x[b][tau]=[b]x[tau]=0`. Hence sigma=tau+b is again a terminal. Since
`ord(sigma)=ord(tau)+1`, the factorization of tau+m followed by b gives

    ord(sigma+m)>=ord(tau+m)+1
                  =ord(sigma)+d(tau),

so d(sigma)>=d(tau).

For a live N-product from tau+m, its result is a non-Apéry head by the
ideal property proved in the companion note. Its predecessor
sigma=tau+b is therefore a terminal. Its order is at least
`ord(tau)+1`, whereas liveness on N says

    ord(sigma)+d(sigma)=ord(tau)+d(tau)+1.

Thus d(sigma)<=d(tau). If the jumps are equal this equality is exactly
`ord(sigma)=ord(tau)+1`, equivalent to a live T-product. Conversely a
live T-product with equal jumps gives precisely the live N-product.

These monotonicities prove stability of the stated filtrations. Taking
the associated graded deletes the strictly increasing, respectively
strictly decreasing, jump arrows. Equal-jump actions agree by part3,
and their degrees differ by exactly d, proving the common-stratum
identification. Filter the finite Koszul complexes by these module
filtrations. The resulting finite spectral sequences have first pages
the Koszul homology of the associated-graded pieces, proving (1.1)
without any assumption about cancellation or characteristic. QED.

**Corollary 2 (constant jump).** If all terminals have the same jump d,
the successor basis bijection is an actual S-module isomorphism
`N=T` with standard degrees increased by d. In general only the
associated-graded strata are identified. This constant-jump statement
is a sufficient condition and does not supply an automatic cancellation
in the x-first spectral sequence.

## A common-stratum fusion bound

Let a be the high-socle dimension of the numerical Apéry quotient Q,
as in the companion note. The universal module fusion inequality and
(1.1) give, for every field and i>=1,

    beta_i(B)+a C(f-1,i-1)
      <=i C(m-a,i+1)
          +sum_d[beta_i^S(K_d)+beta_(i-1)^S(K_d)].       (2.1)

This is a shared actual-module upper bound for both defect sectors.
The K_d modules may have characteristic-dependent Betti numbers;
(2.1) is valid in each characteristic with its actual dimensions.

There is also a fully numerical all-field refinement. For an actual
non-x atom y, let r_y count the live T-arrows

    tau -> tau+y

whose two terminals have **equal** jumps. These are precisely the live
y-arrows on the direct sum of the common strata. Put

    kappa_y=t-r_y,   kappa=min_y kappa_y.

If there are no non-x atoms then T=0 and kappa=0.

**Theorem 3 (one-variable stratum compression).** Uniformly over all
fields,

    beta_i^S(T), beta_i^S(N) <= kappa C(f-1,i),           (2.2)

and hence

    beta_i(B)+a C(f-1,i-1)
      <=i C(m-a,i+1)+kappa C(f,i).                     (2.3)

**Proof.** On K_d, multiplication by y is a partial injective coordinate
translation. If its rank is r_(y,d), its kernel and cokernel both have
dimension `length(K_d)-r_(y,d)`. First take y-homology in the Koszul
complex on S, then bound the remaining Koszul homology by its chain
spaces. Pascal gives

    beta_i^S(K_d)
       <=[length(K_d)-r_(y,d)] C(f-1,i).

Sum over d, use (1.1), and choose the actual variable with largest
sum_d r_(y,d)=r_y. This choice and all ranks are field independent.
The module fusion bound then gives (2.3). QED.

The scalar kappa is the number of constant-jump y-strings for a best
actual variable y in the common-stratum modules, not the number of
original x-strings. Strict jump arrows are discarded in this bound;
they are not silently interpreted as commuting arrows.

## Exact target consequences

In the canonical-pruning setting of the companion note, c is the
number of deleted actual linear socle atoms, e=f+c, delta=m-e, and
`a>=c`. The same all-row proof, substituting kappa for t, gives:

    f kappa <= c delta+(a-c)(2m-a-c+1)/2                 (3.1)

implies P14 for the final source against its actual ordinary target,
in every row and over every field. The actual module inequality (2.1)
can be used in the still sharper row budgets(4.5) of the companion note.
For an arbitrary ordinary source without pruning,

    e kappa <= a(2m-a+1)/2                              (3.2)

is a sufficient all-row certificate.

These are sufficient criteria. No claim that (3.1), (3.2), or the exact
common-stratum budgets hold for every source is made.

## Exact example separating the two numerical fusion bounds

For H=<16,17,39>, all11 terminals have jump2. Its T and N modules have
all-field Betti vectors(1,3,2), independently certified by unit
elimination in actual finite Koszul matrices. Multiplication by the
actual atom17 gives two terminal strings:

    103,120,137,154,171,188,205,222,239;
    142,159.

Thus kappa=2. Deleting the two canonical linear socles79,125 from
Gamma=<16,17,39,79,125> gives this H, with

    f=3, c=a=2, delta=11, t=11.

The length-only fusion bound fails its first-row payment:33>22.
The stratum-compressed criterion pays it: f*kappa=6<=22.
The true source Betti vector is(1,14,36,39,20,4), independently certified
in all fields. This source remains inside inherited small-e/t-only
coverage; it demonstrates a strict improvement between proof
certificates and is not claimed as new historical P14 coverage.

## Unbounded obstruction to automatic positive fusion payment

The corrected common-stratum construction does not make its sufficient
row budgets automatic. There is an explicit obstruction of unbounded
embedding dimension, using the already paid R54 base-four family.
The new assertion here is its canonical-pruning/jump-stratum analysis,
not a new construction or new P14 coverage for that family.

For k>=2 set

    a_i=4^i (0<=i<k),   m=3*4^(k-1)+1,
    L={a_i},   P={a_i+a_j:i<=j},
    Gamma_k=<m, m+a_i, 2m+r:1<=r<m, r notin L union P>.

The accepted R54 exact coordinate theorem gives, over every field,

    delta=C(k+1,2),   e=m-delta,
    t_Gamma=m-C(k+2,2),
    T_Gamma=B_(>=3) with degrees decreased by2,

where

    B=k[Z_0,...,Z_(k-1)] /
       (Z_i^4 (i<k-1), Z_top^3 Z_i (all i)).

All finite x-strings have jump2. All big variables act by zero on T;
the small variables act by B multiplication. The rectangular part of B
is

    R=k[Z_0,...,Z_(k-1)] /
       (Z_i^4 (i<k-1), Z_top^3),

and `B=R direct_sum k*Z_top^3` on coordinates. Within `B_(>=3)`,
the extra monomial is an isolated socle summand; this does not assert
an algebra splitting of B.

**Proposition 4.** Gamma_k has exactly one actual linear global-socle
atom, namely `z=3m-1` (the big atom of offset m-1). Canonical deletion
leaves H_k with

    c=a=1,   f=e-1,   t_H=m-C(k+2,2)-1,
    T_H and N_H isomorphic, after degree shifts, to M=R_(>=3).

In particular

    kappa=3*4^(k-2),   mu_S(M)=C(k+2,3)-1.              (4.1)

Consequently the kappa sufficient criterion (3.1) fails for every k>=2,
and the actual positive module-fusion row budget (4.5) of the companion
note also fails already in row1. The embedding dimension is unbounded;
k=5 gives m769,e754.

**Proof.** A small actual atom has a live square; x is not a socle.
A big linear coordinate can be killed by x only if its offset has
base-four digit sum3. The terminal-module description shows that it
is globally killed precisely if the corresponding cubic B-monomial
is a socle. The B-socles are the extra monomial `Z_top^3` and the
rectangular top monomial

    Z_top^2 product_(i<k-1) Z_i^3.

The latter has degree `3k-1>=5`. Thus the only cubic socle is
`Z_top^3`, whose offset is m-1 and whose big atom is3m-1. This proves
the exact canonical c=1 statement.

Delete it. The accepted canonical theorem preserves every old order
and removes exactly its length-one finite string. Removing the isolated
monomial `Z_top^3` from T gives precisely `M=R_(>=3)`, with its usual
B-module action. All remaining strings retain jump2, so Corollary2
identifies N_H with T_H after shifting degrees. The numerical Apéry
quotient Q_H kills every degree>=3 R-monomial: it is the successor of
one of these remaining terminals. The extra `Z_top^3` instead becomes
numerical Apéry, because its predecessor3m-1 was deleted. It is the
only high socle surviving in Q_H, so a=1=c.

For any lower small variable Z_i, i<k-1, the constant-jump y-strings of
M are counted by its monomials killed by that variable, namely the
rectangular monomials with exponent_i=3. There are
`3*4^(k-2)`; their degree is already>=3. For Z_top the count is
`4^(k-1)-1`, since exponent_top=2 and the degree-two monomial
`Z_top^2` alone is excluded from M. Each big actual variable kills M
and gives t_H strings. Therefore the minimum is exactly the kappa in
(4.1).

All cubic rectangular monomials generate M, and there are
`C(k+2,3)-1` of them: only `Z_top^3` is excluded in degree3.
This proves its exact minimal-generator count over the actual S.

The scalar budget is K=c*delta=delta. For k=2, f*kappa=27>3.
For k>=3, f>=1 and `kappa=3*4^(k-2)>C(k+1,2)=delta`
(the inequality begins at12>6 and persists under the factor4
recursion), so f*kappa>K. The first-row positive module budget is
also exactly delta. For k>=3,

    beta_1^S(N_H)+beta_0^S(T_H)
      >=mu_S(M)=C(k+2,3)-1>C(k+1,2)=delta.

For k=2, mu(M)=3=delta and beta_1(N_H)>0, since a nonzero finite-length
module over a positive-dimensional polynomial ring cannot be free.
Thus that budget fails for all k>=2. QED.

The final Gamma_k remains paid by the inherited linear-x-head theorem:
all its finite x-string heads have degree one. No claim of a genuine
P14 counterexample is made. What is ruled out is the universal claim
that either the corrected common-stratum scalar payment or the
positive N/T module-fusion budget holds automatically. A universal
proof along this route must capture cancellations, beyond merely
adding those two actual module Betti contributions.

## An exact obstruction to both naïve Betti-domination directions

The common filtration theorem cannot be replaced by either global
module identification or universal Betti domination between N and T.
Take the actual numerical source

    H=<35,40,42,91,165,268>.

It has25 finite x-strings and terminal jumps2 and4. A live T-arrow
from terminal131 by atom165 reaches terminal296, raising its jump
from2 to4. Conversely the live N-arrow

    [289+35] --[42]--> [331+35]

corresponds to a decrease from jump4 to2. These two arrows alone
refute a globally commuting successor basis bijection in both
possible directions of multiplication.

The actual finite Koszul complexes on the five non-x variables have
all-field Betti vectors

| Module | beta0 | beta1 | beta2 | beta3 | beta4 | beta5 |
|---|---:|---:|---:|---:|---:|---:|
| N |3|15|30|30|15|3|
| T |3|14|29|32|18|4|
| K_2 |2|10|20|20|10|2|
| K_4 |1|6|14|16|9|2|
| K_2 plus K_4 |3|16|34|36|19|4|

Thus beta1(N)>beta1(T), while beta3(N)<beta3(T). Neither coefficientwise
comparison is universally valid. Both are bounded by the common-stratum
sum, as Theorem1 requires.

These are exact all-field arithmetic certificates, not rank
experiments in a few characteristics. The fresh verifier constructs
the coordinate multiplication matrices, splits Koszul complexes by
standard degree and numerical weight, and performs integer unit-pivot
elimination. Every boundary matrix reduces to zero residual after its
unit pivots. Therefore every displayed rank is unchanged over every
field. `JUMP_FILTRATION_CERTIFICATE.json` records the vectors and the
strict arrows, along with47 other actual finite Koszul checks,35
random multiple-jump profiles, and the base-four controls through k5.

## Two active variables: an exact all-field corner refinement

Choose two distinct actual non-x variables y,z; assume f>=3. On the
common jump strata define

    q=sum_d dim K_d/(y,z)K_d,
    s=sum_d dim (ann_(K_d)y intersect ann_(K_d)z).

Both are exact field-independent coordinate counts. The first is the
number of stratum coordinates outside the union of live incoming
arrows by y,z; the second is the number with no live outgoing arrow
by either. All arrows here retain the terminal jump.

**Theorem 5 (two-variable fusion).** In every field,

    beta_i^S(N), beta_i^S(T)
      <=q C(f-2,i)+s C(f-2,i-1),                        (5.1)

and consequently

    beta_i(B)+a C(f-1,i-1)
      <=i C(m-a,i+1)+q C(f-1,i)+s C(f-1,i-1).           (5.2)

In the canonical-pruning setting, the single numerical condition

    (f-1)q+s <= c delta+(a-c)(2m-a-c+1)/2               (5.3)

pays the actual ordinary target in every row and every field.

**Proof.** The zeroth and second Koszul homologies of a finite module
K_d on y,z have dimensions q_d and s_d. Euler characteristic of its
finite two-variable Koszul complex gives

    dim H_1=q_d+s_d.

Thus their exact polynomial, over every field, is

    q_d+(q_d+s_d)u+s_d u^2=(1+u)(q_d+s_d u).

Now first take y,z-homology, and bound the remaining f-3 variable
Koszul homology by its chain spaces. Sum over d and apply the opposite
filtration theorem. The result is

    P_N, P_T <= (1+u)^(f-2)(q+s u),

which proves (5.1). The positive fusion cost is bounded by one further
factor(1+u), giving (5.2). For1<=i<=f, its coefficient divided by
`C(f-1,i-1)` is

    q(f-i)/i+s <= (f-1)q+s.

The target payment proved in the companion note has at least K times
that binomial weight, so (5.3) pays every row. Higher rows vanish as in
that proof. QED.

For the actual H=<16,17,39> witness, taking y17,z39 gives q1,s2.
The scalar cost becomes4, improving the one-variable cost6 and the
uncompressed length cost33. These are comparisons between sufficient
certificates for an already paid source.

For any r actual variables E, the fully general correct statement is

    P_N, P_T <=(1+u)^(f-1-r) sum_(j=0)^r b_j(E)u^j,

where `b_j(E)=sum_d dim H_j(K_E(K_d))` are the actual finite common-stratum
Koszul dimensions. Hence the fusion cost has one further(1+u) factor.
For r=3 the two middle dimensions must retain their actual ranks;
field independence is not inferred from coordinate matrix entries.
This is an exact all-field statement with field-specific b_j(E), and
becomes a uniform certificate when those ranks have integral unit/Smith
certificates. No outside-variable action is assumed to vanish.

The obstruction persists even if one replaces the high-socle upper
bound for Q_H by its exact first Betti number. For k>=3, let
`b=t_H=m-C(k+2,2)-1` and `mu=C(k+2,3)-1`. The Q_H presentation has
all quadratics involving its b big variables, all core cubics except
`Z_top^3`, and `Z_top^4`. Hence

    beta_1(Q_H)=C(f,2)-delta+mu+1.

The b big variables kill M, so tensoring their zero-action Koszul
complex gives `beta_1(N_H)>=b*mu`. Therefore the exact-Q positive
fusion upper is at least

    C(f,2)-delta+1+(b+2)mu.

This exceeds the actual old-alphabet first-row budget
`C(m-1,2)+delta-1`: the difference is at least

    (b+2)mu+2-delta(2m-delta+1)/2 > 0.                   (4.2)

To see the strict inequality uniformly, for k>=3 one has
`mu>=3delta/2` and `m>=3(delta+k)` (both begin at k3 and the latter
persists under the factor4 growth). Since `b+2=m-delta-k>=2m/3`,
`(b+2)mu>=m*delta`, while the subtracted quantity is
`m*delta-delta(delta-1)/2`. Thus even exact-Q Betti input cannot make
this positive fusion addition automatic. The overestimate must be
reduced by actual cancellations or a different structural bound.
