# Principal scalar theorem: fixed cutoff D=delta and an analytic tail

## Statement

Assume the actual residue-disjoint diagonal resource proved in
`../birth/RESIDUE_DISJOINT_TOWER_OCCUPANCY.md`:

\[
 H_0=\delta,\quad 0\le H_t\le m-1,\quad
 \sum_{t\ge0}H_t\le\delta V,
 \qquad V=e+\delta/2-3/2,\quad m=e+\delta.
\]

For `r>=3` define the actual first scalar

\[
 F_r(H)=(r-1)H_0+\frac{r+1}{2}H_1
                     +\sum_{t\ge2}\frac{r-1}{t+1}H_t.
\tag{1}
\]

The coefficient of H1 includes its exact extra first-birth contribution.
Let `p(delta)` be the largest integer r with `r(r+1)/2<=delta`.

**Theorem.** For all integers `delta>=10`, `e>=274`, and
`3<=r<=p(delta)`,

\[
 F_r(H)\le\delta(V+1).
\tag{2}
\]

For `delta>=210`, the numerical envelope already satisfies (2) for
every `e>=2`.  All statements are about a relaxed nonnegative occupancy
space, so they apply to every actual source satisfying the input.

Actual independent cuts retain their actual size, at most e-1.  If
`p(delta)>e-1`, its use here is solely as a larger numerical value of r:
the scalar is nondecreasing in r.  No overlarge independent cut is
constructed.  The theorem is equivalently an all-r scalar theorem on
`r>=4,delta>=r(r+1)/2,e>=274`, with the monotone rank envelope used below.

## 1. A single fixed cutoff gives an affine embedding ray

Write `M=m-1=e+delta-1` and `H_delta=sum_(u=1)^delta 1/u`.
Choose the fixed harmonic cutoff `D=delta` and put
`alpha=(r-1)/(delta+1)`.  Every tail weight at t>=D is at most alpha,
and the earlier tail corrections are nonnegative.  Consequently

\[
 F_r(H)\le U:=\alpha\delta V+(r-1-\alpha)\delta+BM,
\tag{3}
\]

where the retained first-birth coefficient gives exactly

\[
 B=1+(r-1)(\mathrm H_\delta-1)-\alpha(\delta-1).
\tag{4}
\]

The target-minus-bound gap is the following exact affine function of e:

\[
 G:=\delta(V+1)-U
   =AM-\frac{\delta(\delta+r-2)}2+\delta\alpha,
\quad
 A=\delta+r-2-(r-1)\mathrm H_\delta-\alpha.
\tag{5}
\]

Equivalently, with

\[
 h_\delta=\frac{\delta+r-2}{2}-(r-1)\mathrm H_\delta,
\]

there is the useful exact identity

\[
 G=(e-1)\left[\frac{\delta+r-2}{2}-\alpha\right]
       +(e+\delta-1)h_\delta.
\tag{6}
\]

## 2. Exactly 200 finite-defect infinite rays

The scalar and the upper bound (3) are nondecreasing in r.  Therefore
it is enough to use the numerical envelope r=p(delta).  For each of
the 200 integers `10<=delta<=209`, the companion script checks (5)
at e=274 in exact rational arithmetic, and checks A>0.  These two
strict inequalities prove the entire affine ray e>=274.  No finite-e
sampling or extrapolation is involved.

The companion certificate contains all 200 exact rows, their canonical
digest, the minimum initial gap, and the minimum slope.  It is generated
by `verify_fixed_delta_scalar.py`.  Its finite checks are checks of
coefficients in a universal inequality, not a numerical-semigroup
enumeration.

## 3. Analytic tail for all delta>=210

First prove, for every integer r>=20 and `a_r=r(r+1)/2`,

\[
 \mathrm H_{a_r}\le\frac{r+4}{4}.
\tag{7}
\]

The base is the exact finite rational inequality `H_210<6`, recorded
in the certificate.  For the induction step there are r+1 new terms,
each at most `1/(a_r+1)`, so

\[
 \mathrm H_{a_{r+1}}-\mathrm H_{a_r}
    \le\frac{r+1}{a_r+1}\le\frac14.
\]

The last inequality is `r^2-7r-6>=0`, true for every r>=20.
This proves (7).

For fixed r>=20 and any integer delta>=a_r, the function h_delta in
(6) is nondecreasing, since

\[
 h_{\delta+1}-h_\delta
       =\frac12-\frac{r-1}{\delta+1}>0.
\]

At its initial point (7) gives h_(a_r)>=0, because

\[
 \frac{a_r+r-2}{2}=\frac{(r-1)(r+4)}4.
\]

Thus h_delta>=0 throughout this range.  The bracket in (6) is strictly
positive: `alpha=(r-1)/(delta+1)` is smaller than `(delta+r-2)/2`.
For e>=2, equation (6) proves G>0.

Finally, for every delta>=210 its envelope r=p(delta) is at least20
and delta>=a_r.  This proves the entire analytic tail.  Together with
the 200 exact affine rays, it proves (2) for all delta>=10 and e>=274.

## Rank and field scope

The birth proof separately establishes that for every actual cut with
r>=4, all its normalized higher rank weights are bounded by (1), and
its ordinary target differences are at least
`delta(V+1)*binom(r-1,j-1)`.  Consequently this scalar theorem pays
every relative rank of that same cut wherever its hypotheses hold.
The r3 case is retained under the separately proved universal triple
theorem; no invalid higher-weight domination is asserted at r3.

The parameter proof itself is rational arithmetic and contains no field
operations or claim of characteristic-independent Koszul ranks.  Its
field scope is that of the explicitly inherited tower and harmonic
inequalities, each valid in the original field.  The finite certificate
does not replace the residue proof or a full global source assembly.

The earlier water-filling proof on 4086 rays plus a dyadic tail remains
an auxiliary independent scalar proof.  The principal proof here uses
exactly 200 affine rays and the separate analytic tail at210; the counts
and arguments are not conflated.
