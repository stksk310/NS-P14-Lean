# R55: Apéry-quotient socles absorb canonical-pruning torsion

## Scope and new point

This note proves a universal all-field replacement for the R54 attempt to
make the lifted deleted gaps actual socles in `G_H/xG_H`. They always
become high socles in a different, canonical Artin algebra: retain only
the **numerical Apéry heads** and quotient out all non-Apéry heads.
The quotient and the discarded part are honest modules. No successor map
is assumed to commute with multiplication.

The resulting fusion inequality is unconditional. The stated numerical
P14 consequences are sufficient criteria, not an unrestricted P14 proof.
In particular, the final criterion need not hold automatically. The
source's actual ordinary interval target is used throughout.

All Betti numbers below are intrinsic, over the polynomial ring on the
actual minimal degree-one alphabet. Write `C(v,j)=binom(v,j)`, zero when
`j<0` or `j>v`, and `T_M(u)=1+sum_(i>=1)i C(M,i+1)u^i`.

## 1. A canonical Artin Apéry quotient of every numerical cone

Let `B=G_H` be the tangent cone of an arbitrary numerical semigroup `H`,
with multiplicity `m`, actual embedding dimension `f`, `x=[m]`, and
`S=k[Y_1,...,Y_n]`, `n=f-1`. Put

    A=B/xB,   T=(0:_B x),   t=dim_k T.

A numerical coordinate `[s]` survives in `A` precisely when it is an
x-head: either `s-m` is absent from `H`, or its x-arrow is dead,
`ord_H(s)>ord_H(s-m)+1`. Let `N` be the coordinate span in `A` of the
heads with `s-m in H`.

**Lemma 1.** `N` is a homogeneous ideal of `A`, has length `t`, and is
supported in degrees at least three. The quotient

    Q=A/N

is a standard graded Artin algebra of length `m` and actual embedding
dimension `n`. Its coordinate basis is exactly `Ap(H,m)`.

**Proof.** If an N-coordinate of weight `s` multiplied by an actual atom
`a` survives in A, the resulting head has weight `s+a`, and
`(s+a)-m=(s-m)+a in H`. The result is therefore again in N. A zero
product is harmless. Hence N is an ideal, integrally on numerical
coordinates and over every field.

Every finite x-string has a unique terminal `tau`. Its successor
`tau+m` is a non-Apéry head; conversely every non-Apéry head arises in
this way, because the predecessor exists and its x-arrow is dead. This
is a bijection on **bases**, used only for counting; no module-map claim
is made. Therefore `length N=t`. Such a terminal is positive: the arrow
out of 0 is live. Consequently

    ord(tau+m)>=ord(tau)+2>=3.

The other heads are precisely the m numerical Apéry coordinates. Their
quotient has length m, and deleting N removes no degree-zero or
one coordinate. Thus Q remains standard graded with actual embedding
dimension f-1. QED.

Define the **Apéry high-socle count**

    a=dim_k direct_sum_(d>=3) soc(Q)_d.

It is field independent: multiplication by each actual variable on Q
is a partial injective coordinate translation, so its kernel is a
coordinate span. The common kernel is a coordinate span as well.
This does not identify `a` with the high-socle count of A. The two
counts need not agree.

## 2. Universal module and length fusion inequalities

**Theorem 2.** For every numerical semigroup H, every field, and every
i>=1,

    beta_i(B)+a C(f-1,i-1)
      <= i C(m-a,i+1)+beta_i^S(N)+beta_(i-1)^S(T)         (2.1)
      <= i C(m-a,i+1)+t C(f,i).                         (2.2)

No Cohen--Macaulay, Buchsbaum, pruning, or socle hypothesis on B is used.

**Proof.** The x-first Koszul spectral sequence gives

    beta_i(B)<=beta_i^S(A)+beta_(i-1)^S(T).

The long exact Tor sequence of the actual short exact module sequence
`0 -> N -> A -> Q -> 0` gives

    beta_i^S(A)<=beta_i^S(Q)+beta_i^S(N).

R54's all-field high-socle compression theorem applied to Q, whose
length is m and embedding dimension f-1, gives

    beta_i^S(Q)+a C(f-1,i-1)<=i C(m-a,i+1).

These prove (2.1). Each Koszul chain space of a length-t module on
f-1 variables has dimension `t C(f-1,j)`. Bounding both homologies by
their chain spaces and using Pascal proves (2.2). This argument uses
actual modules N and T, without identifying them. QED.

The module version (2.1) can be much smaller than the length version.
Its field-specific values require actual Koszul/Smith computation;
the length version is already uniform over all fields.

## 3. Canonical pruning gives high socles in Q without a CM hypothesis

Let `Gamma` be any numerical semigroup with c>0 actual linear
global-socle atoms Z. Delete all of them. The accepted R53 canonical
pruning theorem gives

    H=Gamma minus Z,   G_Gamma=G_H ltmes k(-1)^c,
    f=edim(H),   e=f+c,   delta=m-e.

Every old order is preserved, every `z in Z` is a pseudo-Frobenius gap
of H, and `ord_H(z+b)>=3` for every actual atom b of H.

**Lemma 3.** The c coordinates `[z+m]` give c distinct independent
high socles of the Artin algebra Q of Section 1. In particular `a>=c`.

**Proof.** Since z is absent and z+m belongs to H, `z+m in Ap(H,m)`.
Its order is at least three. For an old atom b, the weight `z+m+b`
has predecessor `z+b in H`, so it is not numerical Apéry. If the
product is live, it is either already an x-image (zero in A) or a
non-Apéry x-head (zero in Q). If it is dead, it is also zero. Thus the
class `[z+m]` is a high socle of Q. The weights are distinct. They
also have distinct residues: if two actual atoms z<z' had difference
qm, then z'=z+qm would be decomposable in Gamma. QED.

This repairs the precise false inference isolated in R54: a live
product of `[z+m]` need not be an x-image in B, but its surviving head
always belongs to N. Quotienting N, rather than declaring it absent,
is the necessary correction.

Since a>0, Q has a nonzero degree-two coordinate in addition to its
constant and f-1 linear coordinates; that coordinate is not a high
socle. Hence `m-a>=f+1`. With a>=c this gives `delta>=1`.
Each deleted atom has z>2m, since `ord(z+m)>=3`; therefore the final
source Gamma has its **actual ordinary target T_m**.

## 4. Exact old-alphabet budget and a first-row-optimal scalar payment

The accepted exact actual-alphabet socle-extension identities imply

    T_m-P_(G_Gamma)
      =(1+u)^c [ T_(m-c)-P_B
                   +c u sum_(j=f)^(m-c-2) (1+u)^j ].   (4.1)

Indeed this is R54's exact subtraction, using
`(1+u)^(m-1)-(1+u)^e = u(1+u)^c sum_(j=f)^(m-c-2)(1+u)^j`.
For delta=1 the sum is empty. Formula (4.1) displays the full positive
payment available in the **old actual alphabet**. The budget is not a
claim that H's true interval target is ordinary or has multiplicity
m-c.

**Theorem 4 (non-CM canonical-pruning fusion payment).** In the setting
of Section 3, put

    K=c delta+(a-c)(2m-a-c+1)/2.

If

    f t <= K,                                          (4.2)

then Gamma satisfies P14 over every field and in every row, against its
actual ordinary target T_m. In particular the simpler condition

    f t <= c delta                                     (4.3)

suffices. Neither condition involves the high-socle count of A or the
false premise that the pruned base is Cohen--Macaulay.

**Proof.** For 1<=i<=f, insert (2.2) in the bracket of (4.1). Its i-th
coefficient is at least

    i[C(m-c,i+1)-C(m-a,i+1)]
       +a C(f-1,i-1)-t C(f,i)
       +c sum_(j=f)^(m-c-2) C(j,i-1).                   (4.4)

The first term equals

    sum_(v=m-a)^(m-c-1) v C(v-1,i-1).

All v in the sum satisfy v>=m-a>=f+1. All j in the last sum are at
least f. Binomial monotonicity, the delta-1 terms of the last sum, and
`C(f,i)=(f/i)C(f-1,i-1)` show that (4.4) is at least

    [sum_(v=m-a)^(m-c-1) v+a+c(delta-1)-ft/i]
      C(f-1,i-1)
    =[K-ft/i] C(f-1,i-1)>=0.

For i>f the old source Betti coefficient is zero, and the old budget is
nonnegative. Thus the bracket of (4.1), and then its convolution by
`(1+u)^c`, is coefficientwise nonnegative. QED.

The scalar K is optimal **for the first row of the length-only fusion
bound (2.2) and the explicit old budget (4.1)**: comparison of those
first rows is exactly ft<=K. This is not optimality for actual source
Betti numbers. The universal module version (2.1) gives the still
sharper explicit sufficient row budgets

    beta_i^S(N)+beta_(i-1)^S(T)
      <= i[C(m-c,i+1)-C(m-a,i+1)]
          +a C(f-1,i-1)
          +c sum_(j=f)^(m-c-2) C(j,i-1).                (4.5)

The module budgets are sufficient only; no universal bound establishing
them is asserted.

## 5. A direct ordinary theorem without pruning

The same proof, formally setting c=0 and f=e, gives the following
independent useful formulation.

**Corollary 5.** Let G be any actual ordinary-target numerical tangent
cone, with multiplicity m, embedding dimension e, t finite x-strings,
and a high socles in its numerical Apéry quotient Q. If

    e t <= a(2m-a+1)/2,                                 (5.1)

then all its intrinsic Betti rows are paid by T_m over every field.
This is a sufficient structural certificate, not a universal numerical
inequality. It is the exact first-row condition from (2.2); the proof
above shows why that one scalar condition pays every higher row.

## 6. Exact examples and the remaining obstruction

1. For `H=<8,25,39>`, R54 already proved

       B=k[x,y,z]/(yz,y^6,z^4,xz^3),   t=1.

   Here N is the single coordinate y^5 of weight125, whereas T is
   z^3 of weight117. Thus

       Q=k[y,z]/(yz,y^5,z^4),
       soc(Q)_(>=3)=k*y^4 + k*z^3,   a=2.

   The two canonical gap atoms Z={92,109} give
   `Gamma=<8,25,39,92,109>`, f=3,c=2,e=5,delta=3. The old gate fails:
   `h_A=2<t+c=3`. The new unconditional structural route pays:
   `ft=3<=c delta=6`. This shows that Theorem 4 removes that high-socle
   premise, including a genuine non-CM Buchsbaum base. This source was
   already within inherited small-e and t-only coverage; no new P14
   coverage is claimed from this witness.

2. The conditions do **not** become automatic under canonical pruning.
   For `H=<16,17,39>`, its Apéry weights by residues0,...,15 are

       0,17,34,51,68,85,102,39,56,73,90,107,124,141,78,95.

   Its 11 finite-string terminals are

       103,120,137,142,154,159,171,188,205,222,239.

   The high Q-socles are exactly the two weights95 and141. The gap
   atoms79 and125 have every old/new pair sum of old order>=3, so
   `Gamma=<16,17,39,79,125>` has exactly those two canonical linear
   socles and the displayed non-CM pruned base. Here

       m=16, f=3, c=a=2, delta=11, t=11,
       ft=33>22=K.

   Thus (4.2), (4.3), and the underlying first-row **upper-bound**
   comparison fail. This is not a P14 counterexample: its final old
   t-only criterion is `e(t+c)=65<=delta(m+1)=187`. The length-only
   quotient-socle payment does not eliminate all torsion payment. The
   companion jump-filtration note proves a stronger numerical gate that
   pays this witness, then gives an unbounded genuine obstruction even
   to the positive actual-module fusion budget.

A deterministic 18,000-draw search constructed10,592 actual canonical
extensions;4,112 failed the old h_A>=t+c gate while satisfying (4.2).
None of those4,112 failed the inherited t-only criterion. Those counts
are finite evidence only and establish no new residual coverage.
The verifier separately checks exact coordinate ideals, lifted socles,
all-row binomial payment identities, and the two displayed witnesses.

## 7. Dependency and global boundary

The new inputs proved here are the canonical numerical Apéry ideal N,
the genuine quotient-socle replacement, the module fusion (2.1), the
length fusion (2.2), and the exact all-row payments (4.2)/(5.1).
The accepted dependencies are the R53 actual-alphabet pruning/extension
identities, the x-first Koszul spectral sequence, and R54's all-field
Artin high-socle compression theorem. The latter uses its named
classical lex/EK inputs; they are not newly proved here.

This does not prove unrestricted P14. The exact obstruction in item2
shows that even this corrected quotient-socle scalar payment is not
universal. A global proof would still need to pay the actual N and T
module Betti terms in (4.5), or supply another structural reduction.
