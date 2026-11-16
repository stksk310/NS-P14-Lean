# Ordinary branch: five anchors instead of 83 profiles

2026-11-09. Bounded follow-up search against the manuscript
`proof_integrated_v2/NS_P14_INTEGRATED_PROOF_JA.md`, Sections 2–11 and 15.
This note leaves that manuscript and its existing certificates unchanged.

**Finding.** The ordinary branch for embedding dimensions 5 through 9 can be
closed by the same scalar method used in Section 11. It needs five small exact
anchor rows and a short feasibility lemma for the actual Apéry quotient. Thus
Section 15's 83 profiles, five infinite-tail anchors, lex-profile construction,
and maximal-first-hit comparison are unnecessary for this branch, conditional
only on the already established Sections 2–10. This does not eliminate any
external theorem used by those sections, and this note is not a Lean proof.

The script `ordinary/verify_ordinary_reduction.py` independently checks all
coefficients of the five quadratic identities and every rational comparison.
It imports no existing checker or certificate. Run:

```sh
python auditability_search/ordinary/verify_ordinary_reduction.py
```

## 1. A full quadratic Apéry quotient forces large multiplicity

Let the source have embedding dimension e, multiplicity m, and non-m generators
g₂,…,gₑ. Use the actual quotient Q from Section 2. If

\[
q_2=\binom e2,
\]

then

\[
m\ge e(e-1)+1,\qquad \delta=m-e\ge(e-1)^2. \tag{O1}
\]

Here and throughout this note δ is the multiplicity deficit. The normalized
dilation d used in the narrow-width argument is a separate parameter and does
not occur in this argument.

**Proof.** The degree-two piece of the polynomial ring on the e−1 non-m
generators has dimension \(\binom e2\). The stated equality means that its
degree-two map to Q has zero kernel. Every quadratic monomial therefore gives
a nonzero Apéry coordinate, and different quadratic monomials give different
coordinates. Distinct Apéry coordinates have distinct residues modulo m.

Put

\[
B=\{0,g_2\bmod m,\ldots,g_e\bmod m\}\subset\mathbb Z/m\mathbb Z.
\]

This has e elements, by the atom-residue argument of Section 3. The residues of
the non-m quadratic monomials are pairwise different. None is 0 or the residue
of an atom: each corresponds to an Apéry element of order two, whereas those
residues have Apéry elements 0 and g₂,…,gₑ of orders zero and one. Consequently
all unordered two-term sums from B, allowing equal summands, are different.

For ordered pairs \((b,c)\in B^2\) with \(b\ne c\), the differences b−c are
nonzero and pairwise different. Indeed, if b−c=b′−c′ then b+c′=b′+c; uniqueness
of the unordered two-term sums forces either b=b′, c=c′ or b=c, b′=c′. The
second case is excluded. There are e(e−1) such ordered pairs and only m−1
nonzero group elements. This proves (O1). □

In particular, for an actual cut with r=e−1 and r≥3, Section 4 gives

\[
q_2\ge a_r:=\binom{r+1}{2}=\binom e2,
\]

so equality holds, and (O1) applies. Since \(r^2>a_r\) for r≥3, the corner

\[
e=r+1,\qquad\delta=a_r \tag{O2}
\]

is impossible for an actual source with r≥3. The cut r=2 is exceptional because
r=max(2,p(q₂)) need not equal p(q₂); it is already handled by Section 9.
We only need the exclusion for r=6,7,8.
No assertion about realizability of an abstract Hilbert profile is used.

## 2. Section 11's bound permits any fixed cutoff

Fix r≥4 and put a=aᵣ. Choose any integer n≥r, and set

\[
\begin{gathered}
\mathcal H_n=\sum_{j=1}^n\frac1j,\quad
\alpha=\frac{r-1}{n+1},\quad c=\frac{r+1}{2}-\alpha,\\
M=e+\delta-1,\qquad\mathcal V=e+\frac\delta2-\frac32.
\end{gathered}
\]

Exactly the weighted subtraction in (S4)–(S5), without any change in its
resource hypotheses, gives

\[
\begin{aligned}
F_r\le U(e,\delta)={}&\alpha\delta\mathcal V
 +(r-1-\alpha)\delta+c(M-a)\\
&+M\sum_{j=2}^{n-1}\left(\frac{r-1}{j+1}-\alpha\right).
\end{aligned} \tag{O3}
\]

The assumptions n≥r imply 0<α<1 and c>0. Coefficients in the displayed sum
are positive, the coefficient at j=n is zero, and later coefficients are
negative. Thus (O3) does not restrict the support of the resource sequence.

Define

\[
G(e,\delta)=\delta(\mathcal V+1)-U(e,\delta).
\]

This is the same gap as in Section 11, evaluated at a different fixed cutoff.
Write

\[
e=r+1+s,\quad\delta=a+t,\qquad s,t\in\mathbb Z_{\ge0}.
\]

Put

\[
g=G(r+1,a),\qquad
A=a-1-(r-1)\left(\mathcal H_n-2+\frac{a+2}{n+1}\right),
\]

and

\[
b=G(r+1,a+1)-g=A+2-\alpha(r-1).
\]

For an arbitrary δ, the coefficient of e in G is
\(A(\delta)=\delta-1-(r-1)(\mathcal H_n-2+(\delta+2)/(n+1))\).
Direct subtraction of (O3) gives

\[
\begin{aligned}
A(a+t)&=A+(1-\alpha)t,\\
G(r+1,a+t+1)-G(r+1,a+t)&=b+(1-\alpha)t.
\end{aligned}
\]

Sum the second identity from 0 through t−1, then add s times the first
identity. This proves the exact identity

\[
\boxed{G(r+1+s,a+t)
=g+sA+tb+(1-\alpha)\left(\binom t2+st\right).} \tag{O4}
\]

The last term is nonnegative for integer s,t≥0. This identity establishes
the full infinite range; it is not an extrapolation from sampled values.

## 3. Five small rational rows

For r=4,…,8 choose the following cutoffs. The last three columns share the
positive denominator in the fourth column. All entries are exact integers.

| r | a | n | denominator L | Lg | LA | Lb |
|--:|--:|--:|--:|--:|--:|--:|
| 4 | 10 | 7 | 280 | 2443 | 762 | 1007 |
| 5 | 15 | 10 | 6930 | 39380 | 28429 | 32209 |
| 6 | 21 | 13 | 72072 | −7479 | 424147 | 439591 |
| 7 | 28 | 17 | 2042040 | −12196485 | 17076937 | 17076937 |
| 8 | 36 | 21 | 739024 | −5070732 | 8418651 | 8250691 |

For every row A>0 and b>0. For r=4,5 also g>0, so (O4) is positive for all
s,t≥0. For r=6,7,8, both g+A and g+b are positive, as seen immediately by
adding the relevant integer columns. The sole point where this positivity
argument fails is s=t=0; (O1) excludes it for actual sources. Hence

\[
F_r<\delta(\mathcal V+1)
\]

for every actual source with 4≤r≤8. This statement also covers embedding
dimensions above 9, but those are already covered by the existing Section 11.

## 4. Coverage and human-audit effect

For an ordinary source with 5≤e≤9, Section 4 gives 2≤r≤e−1≤8. The r=2,3
cases are already proved in Section 9. The table covers all remaining cases,
and Sections 8 and 10 transfer the scalar inequality to every Betti row.
Therefore no part of Section 15 is needed for these embedding dimensions.
The existing e≥10 scalar proof remains unchanged and proves the other
ordinary cases.

The concrete replacement map for a later manuscript revision is:

| Existing location | Replacement in the proof route |
|---|---|
| Section 11 | Append the small-rank lemma (O1)–(O4) and the five anchor rows. |
| Section 15 | Remove its dependence from the main theorem; retain as historical verification if desired. |
| Section 16 | Cite Section 9 for r=2,3, the new lemma for 4≤r≤8, and the existing Section 11 for e≥10. |
| Section 17 | Retire the 83-profile certificate and five tail anchors from the required verification boundary; list the five scalar coefficient checks instead. |

No first-hit, truncated-lex, or infinite-tail statement from Section 15 is
required in this replacement proof route. The replacement does not alter
the narrow-width argument or the normalization of its dilation parameter.

The new human audit has two local obligations: check the elementary
ordered-difference injection for the actual Apéry quotient, and check five
quadratic expansions with the displayed rational constants. The row r=7
has the largest denominator, 2,042,040; its two positive adjacent gaps both
have numerator 4,880,452 over that denominator. These are small exact
arithmetic tasks compared with reviewing the 83-profile enumeration and its
five tail mechanisms. The difficult common foundation—jump strata, the
actual module tower, harmonic Koszul bounds, and transfer to all Betti rows—
is retained. Thus this improves the residual ordinary audit substantially,
without making the entire proof routine to audit.

This note proves a replacement, rather than merely suggesting a search
direction. Incorporating it into the main manuscript would require a
separate editorial pass and independent review; neither is performed here.
