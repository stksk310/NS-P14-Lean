# Independent referee report on the N4 simplification

2026-11-09. This report does not edit the current proof. I inspected
`N4_SEARCH.md`, the existing §12.1–§12.6, and the new checker. I separately
implemented and ran `n4/referee_core_audit.py`; its results are preserved in
`n4/referee_core_audit.json`.

**Verdict:** the proposed replacement is mathematically sound within the
stated true-narrow domain. I found no unresolved gap in the all-d version.
It removes both the separate nonprimitive proof and the finite-m/tail
campaign. The remaining finite content is 196 normalized offset pairs,
with two explicitly handled exceptions. This is still a computational
proof, with the retained external inputs and width-four patch stated below.

## 1. Quantifiers and the actual source

The domain must remain

\[
0<a<b<u,\quad \gcd(a,b,u)=\gcd(m,d)=1,
\quad d\ge1,\quad m\ge du+2,
\quad V=du.
\]

The existing §12.2 F1–F8 is already proved in this domain for all d. Its
core is normalized, `C=k[s,st^a,st^b,st^u]`, while its actual numerical
weight is `nm+dB`. Thus neither primitive-only notation nor sampled
multiplicities enter the source bounds

\[
P_C\le W,\quad R\le W-u,\qquad
(\beta_1,\beta_2,\beta_3,\beta_4)
\le(P_C+\sigma_C+1+R,\ 2P_C+\sigma_C+3R,\ P_C+3R,\ R).
\]

In particular, the all-d argument keeps the actual kernel compensation
from F8. It does not substitute core Betti numbers directly for actual
Betti numbers, assume Cohen–Macaulayness, or use the false bound
`P_C+R <= W`.

The all-d unification is valid because the explicit lower capacities

\[
L_1(V)=\binom V2+1,\quad
L_2(V)=2\binom V3+V,\quad
L_3(V)=3\binom V4+\binom V2\ (V\ge5),\quad
L_4(V)=4\binom V5
\]

are nondecreasing in V. It is sufficient to use these particular lower
bounds; no claim about the monotonicity of an arbitrary fixed-m residue
formula is necessary.

## 2. The Kneser step is valid, including composite widths

Put `A={0,a,b}` in the cyclic group of order u. For n>=1 with nA proper,
let H be the stabilizer of nA. The n-fold form of Kneser's theorem gives

\[
|nA|\ge n|A+H|-(n-1)|H|.
\]

If H is trivial this is `2n+1`. If H is nontrivial, it is proper and A
cannot lie in H: A contains 0 and generates the whole group. Therefore
`|A+H| >= 2|H|`, and the lower bound is at least
`(n+1)|H| >= 2n+2`. This proves

\[
|nA|\ge\min(u,2n+1).
\]

The n=0 case is separate and immediate. Since 0 pads words, nA is exactly
the set of residues having shortest internal-word length at most n. Hence

\[
W=1+\sum_{n\ge0}(u-|nA|)
\le1+\lfloor u^2/4\rfloor.
\]

This is a universal argument, with no prime-width assumption. The new use
of Kneser must remain an explicit dependency. Kneser is already an input
elsewhere in the current complete proof, so it adds an N4 application but
does not add a new external theorem to the overall project.

## 3. All higher rows check

The bounds in the proposal follow exactly:

\[
\beta_2\le5W-2u-1\le5u^2/4-2u+4,\quad
\beta_3\le4W-3u\le u^2-3u+4,\quad
\beta_4\le W-u\le u^2/4-u+1.
\]

I independently expanded the three gap polynomials using exact symbolic
arithmetic. The resulting coefficient lists, in increasing powers of z,
are

| Difference | Substitution | Coefficients |
|---|---|---|
| `12*(L2-U2)` | `u=6+z` | `108,152,45,4` |
| `8*(L3-U3)` | `u=5+z` | `88,134,67,14,1` |
| `60*(L4-U4)` | `u=5+z` | `105,458,435,170,30,2` |

All coefficients are positive, giving the asserted infinite ranges.
For u=5 the floor gives W<=7 and beta_2<=24<25=L2(5).

For u=4, F2 alone gives `H_x <= u-2 = 2`, so F6 gives R=0.
Kneser gives P_C<=5. A two-variable downset of length at most 5 cannot
have three socle monomials, so sigma_C<=2. The resulting upper bounds
are `(beta_2,beta_3,beta_4) <= (12,5,0)`. At physical V=4 the target
minima are `(12,7,positive)`; at V>=5 the displayed lower capacities
are larger. This is uniform in d.

For u=3 the only pair is (1,2). Directly
`Q_C = k[y,z]/(y,z)^2`, so `(P_C,sigma_C,R)=(3,2,0)` and the higher
upper bounds are `(8,3,0)`. At d=1 source equals target; at d>=2 the
physical width is at least 6 and the target pays them immediately.

Thus no finite-m points or tail certificates remain for the higher rows.

## 4. The new first-row cutoff 13 is correct

For a two-variable downset with s socle monomials, list the socle
exponents in increasing y exponent. The i-th y exponent is at least i,
and its z exponent is at least s-1-i. Therefore every monomial of total
degree s-1, and every divisor of those monomials, lies in the downset.
Consequently

\[
\binom{s+1}2\le P_C.
\]

The retained Savchev–Chen argument applies directly to words having no
endpoint representation. It does not require the old two-face initial
ideal or five-support argument. With h=floor(u/2), the mixed words
contribute at most C(h,2), and the pure axes at most 2u-3, so

\[
P_C\le B_{cap}=\binom h2+2u-3.
\]

For u=2h this is C(h+4,2)-9; for u=2h+1 it is C(h+4,2)-7. The socle
inequality therefore gives sigma_C<=h+2. Substitution into F8 and the
W bound yields the first-row capacity gaps

\[
\frac{h(h-7)}2\quad(u=2h),\qquad
\frac{h^2-5h-2}2\quad(u=2h+1).
\]

They are nonnegative for even u>=14 and odd u>=13. Thus all u>=13,
all d, and all permitted m are covered on paper. The equalities and
thresholds in the candidate are correct.

## 5. Independent finite audit: 196 pairs, not 593

My checker imports neither the historical code/certificates nor the new
candidate checker. It computes the core in two ways and compares their
`P_C, sigma_C, H_x` for every offset:

1. Complete degree-offset sets for the alphabet `{0,a,b,u}`. An internal
   word of degree n and offset B survives modulo the endpoints exactly
   when B is absent from both the degree n-1 offset set and its u-shift.
2. Independently enumerate internal words of length at most u-1, form
   their `(residue,L,K)` coordinates, and take the Pareto minima in every
   residue. Socle multiplication is then calculated in coordinates.

The finite core-generation cutoff u-1 follows from the existing prefix
zero-sum argument. Both implementations agree. Breadth-first search in
the cyclic group separately computes W. The actual all-m bound evaluated
is

\[
\widehat R=\min(W-u,\ u\max(H_x-2,0)),\quad
U_1=P_C+\sigma_C+1+\widehat R.
\]

| u | Primitive pairs | Minimum `C(u,2)+1-U1` |
|---:|---:|---:|
|3|1|-2|
|4|3|-1|
|5|6|1|
|6|9|0|
|7|15|2|
|8|18|4|
|9|27|7|
|10|30|8|
|11|45|14|
|12|42|12|
|Total|196||

I also checked the superseded range 3<=u<=16. Its correct count is 493;
the same two exceptions occur. The initially mentioned count 593 is
incorrect. The stronger socle bound makes that larger range unnecessary.

The only failures are `(u,a,b)=(3,1,2)` with U1=6 and `(4,1,3)` with
U1=8. They are failures of this coarse comparison against minimum target
capacity, not counterexamples to N4. At d>=2 their actual physical widths
are at least 6 and 8, with first-row capacities at least 16 and 29. At
d=1,u=3 source and target coincide. Only d=1,u=4 needs the retained patch.

This computation enumerates no multiplicities. Its universal m,d scope
comes from the proved F6/F8 inequalities. It must not be described as a
finite-m experiment promoted to a universal statement.

## 6. Width-four patch independently checked

For d=1,u=4,(a,b)=(1,3), the allowed domain is m>=6. I checked the
existing B2–B4 formulas and recomputed the monomial-generator counts.
At m=6 the initial ideal has six generators and F1=9. At m>6 put
`theta_n=ceil((m-n)/4)`. The four extra minimality tests in B4 are

`theta1<theta0`, `theta2<theta1`, `theta3<theta0`, `theta6<theta3`.

For `m=4q+r`, r=0,1,2,3, the five theta values `(theta0,theta1,theta2,
theta3,theta6)` are respectively

- `(q,q,q,q,q-1)`;
- `(q+1,q,q,q,q-1)`;
- `(q+1,q+1,q,q,q-1)`;
- `(q+1,q+1,q+1,q,q)`.

Thus the generator counts, including the `xz^2` generator, are
`6,8,8,6`, while the actual target capacities are `7,10,9,8`. This
verifies all m>=6 by residue. **A uniform claim beta_1<=7 is not supplied
by this initial ideal calculation and must not replace the residue
comparison.** The current candidate correctly avoids that claim.

The patch only proves the requested true-narrow domain. The replacement
should not silently enlarge its statement to all m>u: that would add m=5
in this last case and require an additional check.

## 7. Optional further cleanup and completion qualification

The elementary short-word lemma is valid and may be retained. There is
also a way to remove it as a separate prerequisite: the socle antichain
inequality and `P_C<=1+u^2/4` already imply sigma_C<=u-1 for u>=3.
Indeed sigma_C>=u would force `u(u+1)/2<=1+u^2/4`, which is impossible.
For the first-row axis count one can retain just the pure-axis shortening
argument, or its explicit pure-power relation. For u=4 the generic F2
bound `H_x<=u-2` suffices. This is an optional reduction, not a repair
needed for the candidate as written.

The candidate correctly retains arbitrary-field target formulas,
Savchev–Chen, actual kernel compensation, a finite offset certificate,
and the width-four Gröbner patch. It is not yet a Lean proof and does not
eliminate computation altogether. Subject to preserving those
qualifications, I recommend this replacement rather than retaining the
large multiplicity and five-support campaigns.

Reproduction commands used:

```sh
python simplification_search/n4/referee_core_audit.py
python simplification_search/n4/check_shorter_n4.py
```

Both completed successfully. The positive polynomial expansions were
also recomputed independently with exact SymPy polynomial arithmetic.
