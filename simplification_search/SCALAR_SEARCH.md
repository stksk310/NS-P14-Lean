# Scalar proof simplification: two proved replacements

Search scope: `proof_complete/NS_P14_COMPLETE_PROOF_JA.md`, §§10–11 and
Appendix B. The search stopped after the two replacements below. The main
manuscript and its existing checkers have not been changed.

**Verified outcome.** The existing scalar theorem for every integer
`e >= 10`, `r >= 4`, `delta >= r(r+1)/2` has a shorter proof:

1. Freeze the cutoff at a number depending only on `r`. This removes both
   parity cases in the delta direction, the cutoff-change calculation, and
   the delta induction itself. A quadratic identity replaces them.
2. Compare the rank threshold with the elementary barrier
   `r/4 + 1 + 9/(2r)`. This removes the degree-10 rank-difference polynomial
   and its long shifted-coefficient identity.

The same `H_23 < 747/200` anchor and the same six small-rank comparisons
suffice. One new small rational comparison replaces the old `9 -> 10`
threshold comparison. No theorem about numerical semigroups, resource
columns, or Betti numbers is strengthened or replaced here.

## 1. Connection to the existing reduction

Use the original notation, writing `d` for `delta`:

\[
a=a_r=\frac{r(r+1)}2,\qquad M=e+d-1,\qquad
V=e+\frac d2-\frac32,
\]
\[
F_r=(r-1)d+\frac{r+1}{2}H_1
       +\sum_{t\ge2}\frac{r-1}{t+1}H_t.
\]

The earlier proof supplies

\[
H_0=d,\quad \sum_tH_t\le dV,\quad H_t\le M,
\quad H_1\le M-a.
\tag{R}
\]

Sections 8–10 require only `F_r <= d(V+1)`, simultaneously for all ranks
in the relative resolution. All statements in §§2–10, including the
actual-cut bound `d >= a_r`, can therefore be retained exactly as written.

The cutoff need not track `d`. For any fixed integer `n >= 2`, put

\[
\alpha=\frac{r-1}{n+1},\qquad c=\frac{r+1}{2}-\alpha.
\]

If `c > 0`, subtract the tail weight `alpha` from the weights in `F_r`.
For `t >= n` the residual weight is nonpositive and can be dropped. The
remaining positive weights and (R) give

\[
\begin{aligned}
F_r\le U_r(e,d;n)={}&\alpha dV+(r-1-\alpha)d+c(M-a)\\
 &+M\sum_{t=2}^{n-1}\left(\frac{r-1}{t+1}-\alpha\right).
\end{aligned}
\tag{1}
\]

This is exactly the old weighted envelope, with the cutoff left free.
The `H_1` capacity is used once. Summing the finite series gives

\[
U_r=M+(r-1)K_n-ca,
\]
\[
K_n=d+\frac{d(V-1)}{n+1}
     +M\left(\mathcal H_n-2+\frac2{n+1}\right),
\qquad \mathcal H_n=\sum_{u=1}^n\frac1u.
\tag{2}
\]

Define

\[
G_r(e,d;n)=d(V+1)-U_r(e,d;n),
\]
\[
A_r(d;n)=d-1-(r-1)\left(\mathcal H_n-2+\frac{d+2}{n+1}\right).
\tag{3}
\]

As in the current proof, `A_r` is the coefficient of `e` in `G_r`.

**From now on freeze**

\[
n=n_r=\left\lfloor\frac{a_r}{2}\right\rfloor+1.
\tag{4}
\]

Then `n >= r`, `alpha < 1`, and `c > 0` for `r >= 4`. This remains a valid
cutoff in (1) for every `d >= a`, even though it is usually smaller than
the old `floor(d/2)+1`. A larger cutoff is unnecessary once the frozen
envelope itself has been proved sufficient.

## 2. Replacement for the degree-10 rank argument

At the triangular base `e=10, d=a`, direct simplification of (2)–(3)
gives the existing identity

\[
G_r(10,a;n)=(r-1)(a+9)(T_r-\mathcal H_n),
\tag{5}
\]
\[
T_r=\frac{a(a+22-r)}{2(r-1)(a+9)}+\frac{2r-3}{r-1}
       -\frac{a(a+21)+36}{2(n+1)(a+9)}.
\]

Put `epsilon = a mod 2`. Equivalently,

\[
T_\epsilon(r)=\frac{a(a+22-r)}{2(r-1)(a+9)}+\frac{2r-3}{r-1}
       -\frac{a(a+21)+36}{(a+4-\epsilon)(a+9)}.
\]

The numerator of the subtracted term is positive, so
`T_1(r) <= T_r <= T_0(r)`.

For `4 <= r <= 9`, retain the existing six comparisons. Their proof uses

\[
\mathcal H_{23}=\frac{444316699}{118982864}<\frac{747}{200},
\]
\[
\frac{747}{200}-\mathcal H_{23}
 =\frac{2107451}{2974571600}>0,
\]

and, by Cauchy, for `n <= 23`,

\[
\mathcal H_n<\frac{747}{200}-\frac{2(23-n)}{n+24}.
\]

The six margins `T_r - 747/200 + 2(23-n)/(n+24)` are respectively

\[
\frac{17587}{79800},\quad\frac{143}{1200},\quad
\frac{23}{350},\quad\frac{2993}{96200},\quad
\frac{321}{60200},\quad\frac1{900},
\tag{6}
\]

all positive. Thus (5) is positive for `4 <= r <= 9`.

For `r >= 10`, introduce the simpler barrier

\[
B(r)=\frac r4+1+\frac9{2r}.
\tag{7}
\]

The following rational-function identity replaces the old rank-difference
polynomial:

\[
T_1(r)-B(r)=
\frac{N(r)}{2r(r-1)(r^2+r+6)(r^2+r+18)},
\tag{8}
\]
\[
\begin{aligned}
N(r)
 &=2r^5-5r^4-148r^3+111r^2-900r+972\\
 &=r^3\big((r-10)(2r+15)+2\big)
    +r\big(111(r-10)+210\big)+972.
\end{aligned}
\]

Every term on the last line is positive or nonnegative for `r >= 10`.
The denominator is positive. Hence `B(r) < T_1(r) <= T_r`.

It remains to bound the harmonic number by `B(r)`. At `r=10`, `n=28`.
Convexity of `u -> 1/u` bounds a finite sum by the sum of the linear
interpolant between its endpoints. Consequently,

\[
\mathcal H_{28}-\mathcal H_{23}
 \le\frac52\left(\frac1{24}+\frac1{28}\right)=\frac{65}{336},
\]
\[
B(10)-\frac{747}{200}-\frac{65}{336}
 =\frac{79}{20}-\frac{747}{200}-\frac{65}{336}
 =\frac{181}{8400}>0.
\tag{9}
\]

Thus `H_28 < B(10)`.

For the general step write `n_r=floor(a_r/2)+1` and
`b=n_(r+1)-n_r`. Then

\[
b\le\frac{r+2}{2},\quad n_r+1\ge\frac{a_r+3}{2},
\quad n_{r+1}\ge\frac{a_{r+1}+1}{2}.
\]

The same endpoint interpolation gives

\[
\begin{aligned}
\mathcal H_{n_{r+1}}-\mathcal H_{n_r}
&\le\frac b2\left(\frac1{n_r+1}+\frac1{n_{r+1}}\right)\\
&\le\frac{r+2}{2}\left(\frac1{a_r+3}+\frac1{a_{r+1}+1}\right)
 <\frac2r.
\end{aligned}
\tag{10}
\]

Indeed, the difference between `2/r` and the last rational upper bound is

\[
\frac{8(r^2+3r+6)}{r(r^2+r+6)(r^2+3r+4)}>0.
\]

On the other hand,

\[
B(r+1)-B(r)-\frac2r
 =\frac{r^2-7r-26}{4r(r+1)}>0\qquad(r\ge10),
\tag{11}
\]

since `r^2-7r-26=(r-10)(r+3)+4`. Equations (9)–(11) prove
`H_(n_r) < B(r) < T_r` for every integer `r >= 10`. Together with (6),

\[
g_0:=G_r(10,a;n)>0\qquad(r\ge4).
\tag{12}
\]

This proof has no degree-10 polynomial and no comparison of
`T_1(r+1)` with `T_0(r)`. Parity survives only in the harmless definition of
`n_r` and the inequality `T_1 <= T_r`.

## 3. Replacement for the delta parity and cutoff inductions

Continue with the frozen `n=n_r`. Put

\[
A_0=A_r(a;n),\qquad \alpha=\frac{r-1}{n+1}.
\]

The existing base-point identity is

\[
g_0=(a+9)A_0+C,
\]
\[
C=\frac{a[-a(n-r+2)-n(r-4)+3]}{2(n+1)}<0.
\tag{13}
\]

The sign follows from `n >= r`, `a >= 10`, and `r >= 4`: the bracket is
at most `-2a+3 < 0`. Thus (12) gives

\[
A_0>\frac{-C}{a+9}>0.
\tag{14}
\]

Let

\[
b_0=A_0+11-r-8\alpha.
\]

To verify its sign, define

\[
F_\epsilon=\frac{-C}{a+9}+11-r-\frac{8(r-1)}{n+1},
\qquad n=\frac{a-\epsilon}{2}+1.
\]

The old elementary rational identities remain valid:

\[
F_0-F_1=\frac{(r-1)(a^2+17a+144)}{(a+3)(a+4)(a+9)}>0,
\]
\[
F_1=\frac a2-\frac{3r}2+\frac{11}2
 +\frac{3(5r+31)}{2(a+9)}-\frac{17(r-1)}{a+3}.
\tag{15}
\]

For `r >= 4`,

\[
\frac a2-\frac{3r}2+\frac{11}2
 =\frac{r^2-5r+22}{4}\ge\frac92,
\]
\[
a+3-4(r-1)=\frac{(r-3)(r-4)}2+1>0.
\]

The middle positive term in (15) can be discarded, and therefore

\[
b_0>F_\epsilon\ge F_1>\frac92-\frac{17}4=\frac14.
\tag{16}
\]

Now no induction in `d` is needed. For every integer `t=d-a >= 0`, (2)
is quadratic in `d` and (3) is affine in `d`; direct subtraction gives

\[
\boxed{A_r(a+t;n)=A_0+t(1-\alpha)>0,}
\tag{17}
\]
\[
\boxed{G_r(10,a+t;n)=g_0+t b_0+(1-\alpha)\binom t2>0.}
\tag{18}
\]

Here `alpha < 1`, `g_0 > 0`, `b_0 > 1/4`, and `binom(t,2) >= 0`.
For completeness the forward difference of (18) is exactly
`A_r(d;n)+11-r-8(r-1)/(n+1)`, the fixed-cutoff difference already present
in the manuscript. Summing its affine increments yields (18).

Finally, affine dependence on `e` gives, for all integers `e >= 10`,

\[
G_r(e,d;n)=G_r(10,d;n)+(e-10)A_r(d;n)>0.
\tag{19}
\]

Equations (1) and (19) imply `F_r < d(V+1)`, exactly the sufficient
condition required by §10. The conclusion holds for every allowed
`(e,r,d)` and uses the actual cut rank, with no maximum-rank envelope.

## 4. What can be deleted or replaced in the current manuscript

* In §11.1, define the cutoff by (4), independent of `delta`; retain the
  resource-envelope calculation and the affine-in-`e` reduction.
* Retain the triangular-base formula and six small-rank comparisons.
* Replace §11.4 by §2 above. Delete its degree-10 polynomial appendix.
  The old exceptional `r=9 -> 10` threshold comparison is unnecessary;
  (9) is its simpler replacement.
* Delete §11.5, the two parity-dependent slope differences in old (10).
* Replace §11.6 by §3 above. Retain its useful `C` and `F_epsilon`
  calculations, but delete the moving-cutoff step (17). Equations
  (17)–(18) above replace all delta monotonicity induction.

The separate manuscript sentence that very large `delta` needs no
special harmonic induction remains true, but is historical commentary,
not a further argument. Repeated statements that no maximum-rank
envelope is needed can be stated once at the conclusion. Definitions
of `F_r` repeated at the start of §11 are useful if that section is meant
to stand independently; otherwise §10 can simply be cited.

## 5. Exact verification and limitations

Run:

```text
python -B simplification_search/scalar/check_scalar_simplifications.py
```

Observed result on 2026-11-09:

* The new identity (8) was rebuilt from the definition of `T_1` using
  rational polynomials; cross-multiplication matched every coefficient.
  The positive grouping of `N(r)` also matched every coefficient.
* The `H_23` anchor, all six margins (6), and the replacement anchor
  margin `181/8400` were recomputed with exact fractions and were positive.
* All 351 finite diagnostics passed, for `4 <= r <= 30` and
  `0 <= delta-a_r <= 12`, using the frozen cutoff. They checked the
  original finite weighted sum against (2), the triangular base and `C`
  identities, the `F_1` bound, (17)–(19), and positive forward differences.
* The smallest diagnosed gap was `5845533/7436429`; the smallest forward
  gap difference was `3791/630`.

The infinite result follows from the written inequalities and identities
above. The finite diagnostics are supplemental; they are not used to
claim an exhaustive universal check. This is an exact mathematical
proof simplification and arithmetic supplement, not a Lean verification.

No simplification of Appendix B is claimed. The two successful targets
were enough to remove the main scalar proof's two most cumbersome
devices, so no broader search was performed. A small diagnostic probe
also found that merely lowering `e >= 10` to `e >= 9` while preserving the
same scalar envelope fails at `(e,r,d)=(9,8,36)`: its gap is exactly
`-2218033/251940`. This is a failure of that attempted bound, not a
counterexample to the Betti inequality, and is not an accepted candidate.
