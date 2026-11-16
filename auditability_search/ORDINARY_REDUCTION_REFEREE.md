# Independent referee report: ordinary reduction

2026-11-09. Scope: `ORDINARY_REDUCTION.md`, the Japanese paper-facing note
`ORDINARY_PAPER_REDUCTION_JA.md`, and `ordinary/verify_ordinary_reduction.py`,
checked against the frozen V02
`proof_integrated_v2/NS_P14_INTEGRATED_PROOF_JA.md`, Sections 2–11.
The common foundation is assumed established; this report audits the proposed
replacement and its connection to that foundation. No manuscript or checker
was edited for this review.

## Verdict

**The proposed replacement works for its intended range.** For every actual
ordinary source with `4 <= r <= 8`, it proves the scalar inequality for all
integer `e >= r+1` and `delta >= a_r`, with only the three stated base corners
requiring the actual-source feasibility lemma. Combining it with V02 Section 9
and the unchanged Section 11 covers the whole ordinary branch without Section
15's profiles or tails. The result is conditional on the existing Sections
2–11; it is neither a new audit of that entire foundation nor a Lean proof.

**One minor scope issue was found and resolved.** The first reviewed version's
Section 1 said an actual cut `r=e-1` always implies `q_2>=a_r`, and consequently
excluded the base corner for `r>=2`. At `r=2`, the forced definition
`r=max(2,p(q_2))` does not imply `r=p(q_2)`. An actual ordinary counterexample
to that unqualified corner exclusion is `Gamma=<6,7,11>`: `e=3`, `m=6`,
`delta=3=a_2`, and `Q` has Hilbert function `(1,2,2,1)`, so `r=2`. I reported
this immediately. The coordinator restricted the cut implication and corner
exclusion to `r>=3` in both notes, explicitly separated the `r=2` case, and I
verified the patched text. This resolves the issue and never affected the
used ranks 6, 7, and 8. The lemma (O1) itself was correct as stated.

## Actual quotient and characteristic

V02 Section 2 defines `Q=A/N` with one numerical Apéry coordinate for each
residue, in degree equal to its longest factorization length. It is a standard
graded quotient of the polynomial ring on the `e-1` non-m generators. Thus
`q_2=binom(e,2)` makes the degree-two surjection an isomorphism. Every quadratic
monomial has a nonzero image; its image is the coordinate of `g_i+g_j`, which
must be Apéry and have order two. Distinct monomials give linearly independent
coordinates. A non-Apéry sum, an order jump above two, or two identical
coordinates would contradict injectivity.

Consequently, all these sums have distinct residues, and none has residue zero
or an atom residue. Each residue has a unique Apéry representative; its order
cannot simultaneously be two and zero or one. The atoms themselves are Apéry
with distinct nonzero residues, by the minimal-generator argument in V02
Section 3. Therefore all unordered two-term sums, including repeated elements,
of `B={0,g_2 mod m,...,g_e mod m}` are distinct.

The difference injection is valid even when `m` is composite or even. From
`b-c=b'-c'` obtain the equality of unordered pairs
`{b,c'}={b',c}`. The alternatives are the same ordered pair or `b=c` and
`b'=c'`; the latter is excluded. Thus the `e(e-1)` nonzero ordered differences
are distinct, giving `m-1 >= e(e-1)` and `delta >= (e-1)^2`. No division in the
base field, sign-dependent rank argument, generic characteristic assumption,
or prime-modulus theorem enters this reasoning. Characteristic two causes no
exception: distinct polynomial monomials remain independent formal basis
elements, including the squares.

For every actual cut used here, `r>=4` gives `r=p(q_2)`. If `e=r+1`, then
`a_r <= q_2 <= binom(e,2)=a_r`, hence equality and `delta>=r^2>a_r`.
The excluded corners are precisely `(r,e,delta)=(6,7,21),(7,8,28),(8,9,36)`.
The stronger feasibility lower bounds there are `36,49,64`, respectively.

## Resource inequality and exact expansion

The fixed-cutoff bound uses exactly the V02 (S3) hypotheses:

```
H_0=delta, H_t>=0, sum H_t<=delta*V,
H_t<=M, H_1<=M-a_r.
```

It keeps the same scalar `F_r`, total resource, and separate first-layer cap.
The prior transition from `q_2` to `a_r` is already present in V02 (5.4)/(S3);
the supplement makes no further weakening of that cap. There is no replacement
of the actual sequence or reoptimization over Hilbert profiles. Choosing a
different fixed `n` for each of five ranks is legitimate: the weighted
subtraction identity is valid for every `n>=r`. The residual coefficients are
positive for `2<=j<n`, zero at `j=n`, and negative after that. Discarding the
nonpositive terms uses `H_j>=0`, while the positive terms use `H_j<=M`.
The first-layer coefficient is positive and uses its cap once. No support
restriction is introduced.

Independently of the submitted polynomial routines, I simplified the tail to

```
(r-1)*(H_n-3/2) - alpha*(n-2)
```

and used symbolic algebra with `r,n,a,H_n` all independent formal symbols.
Substitution into (O3) gives identically

```
G(r+1+s,a+t)
 = g+s*A+t*b+(1-alpha)*(t*(t-1)/2+s*t),
A = a-1-(r-1)*(H_n-2+(a+2)/(n+1)),
b = A+2-alpha*(r-1).
```

The symbolic remainder was exactly zero; the formula for `A` as the `e`
coefficient and the formula for `b` as the forward difference also agreed
identically. This checks the expansion beyond the five numerical instances.

All table entries independently reproduced. The two adjacent gaps are:

| r | g+A | g+b |
|---:|---:|---:|
| 4 | 641/56 | 345/28 |
| 5 | 3229/330 | 3409/330 |
| 6 | 14881/2574 | 54014/9009 |
| 7 | 1220113/510510 | 1220113/510510 |
| 8 | 3347919/739024 | 3179959/739024 |

In every row `A,b,1-alpha` are positive. For ranks 4 and 5, `g` is also
positive. For ranks 6–8, if `s>=1`, write the linear part as
`(g+A)+(s-1)*A+t*b`; if `s=0,t>=1`, write it as `(g+b)+(t-1)*b`.
Both are positive. The remaining term is nonnegative for **integer** `s,t>=0`.
The integrality qualification matters because `t(t-1)/2` need not be
nonnegative for real `0<t<1`; all actual parameters are integers. This proves
the infinite range, rather than extrapolating a finite sample. The three
remaining `s=t=0` points are excluded above.

## Coverage and checker boundary

For `5<=e<=9`, the actual cut has `2<=r<=e-1<=8`; ranks 2 and 3 are already
covered by V02 Section 9 and ranks 4–8 by the new argument. For `e>=10`, the
old Section 11 covers all actual `r>=4`, while Section 9 still covers 2 and 3.
Equivalently, any `r>=9` has `e>=r+1>=10`. There is no missing rank or parameter
strip. V02 (10.1) and (8.4) then transfer the scalar bound to every relative
rank, including the top rank, and Section 8 transfers those to all ordinary
Betti rows over the same field. The new route uses no statement from Section
15. The unchanged treatment of the very small embedding dimensions is outside
the replacement's burden.

I inspected and ran the submitted checker successfully:

```
python auditability_search/ordinary/verify_ordinary_reduction.py
```

It constructs (O3) by exact rational polynomial arithmetic, checks every
coefficient, compares the computed `g,A,b` against the displayed table, and
checks all needed signs. In particular, the negative base gaps are retained
and checked; they are not silently replaced by positive constants. The
coefficient dictionary check also rules out extra powers. Although its linear
coefficients are extracted before comparing the identity, the explicit table
comparison and the quadratic/mixed-coefficient checks make this a substantive
exact arithmetic test, not an assumption of the desired positive numbers.
It imports no legacy checker or certificate and uses active `require` checks.

As its comments acknowledge, the script does not prove the actual-source
Sidon lemma, the resource hypotheses, or transfer to Betti rows. Those are
mathematical obligations checked above or retained from V02. I also ran
`python proof_integrated_v2/checks/verify_scalar.py` successfully; its symbolic
barrier check and 351 supplementary diagnostics passed. These finite
diagnostics are corroboration, not the proof of the unchanged infinite tail.

I also read the Japanese paper-facing note in full after the scope correction.
Its (SO1)–(SO5), constants, integer qualification, resource hypotheses, and
rank-based connection to Sections 9–11 agree with the audited English route.
Restricting the old Section 11 to `r>=9` would indeed make its first five small
rows redundant: its rank-9 row and rank-10-and-up proof remain. That proposed
editorial restriction is optional and has not been applied. The introductory
claim combining this result with a prior N4 replacement is conditional on
that separate replacement; the N4 work is outside this report's scope.

Reviewed file hashes after the correction and successful checker rerun:

```
df4e3e1544840ae01eedd729588b7a29a852d178f044421949dc9c1005dbd908  ORDINARY_REDUCTION.md
97f6b39cec112aab8d2e94b0c7feb5f2654ada898f61130796bd05fb4871931f  ORDINARY_PAPER_REDUCTION_JA.md
85b8547546d5c88a46a5e608aef72ac78ff7a514bc5843dc05215af98bdf8ec6  ordinary/verify_ordinary_reduction.py
```
