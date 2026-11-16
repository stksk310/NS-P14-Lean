# Bounded referee review: scalar and width simplifications

Reviewed on 2026-11-09. Scope: `SCALAR_SEARCH.md`,
`scalar/check_scalar_simplifications.py`, `WIDTH_SEARCH.md`, and
`width/check_width_candidates.py`, compared with
`proof_complete/NS_P14_COMPLETE_PROOF_JA.md` §§5, 8–11 and Appendices A/C.
This is a review of the proposed replacements and their interfaces, not a
new audit of the complete P14 proof. The existing manuscript was not edited.

**Verdict.** All four proposed replacements are mathematically valid on
their stated integer domains. I found no counterexample, reversed
inequality, missing parameter range, or new restriction on the base field.
The scalar replacements can be adopted together. The two width candidates
are independent and can be adopted separately. The qualifications in §4
below must remain explicit when editing the manuscript.

## 1. Scalar: freezing the cutoff is legitimate

Let
\[
a=r(r+1)/2,\qquad n=\lfloor a/2\rfloor+1,\qquad
\alpha=(r-1)/(n+1),\qquad c=(r+1)/2-\alpha.
\]
For every integer \(r\ge4\), \(n\ge r\), hence
\(0<\alpha<1\) and \(c>0\). These facts depend on \(r\), not on
\(d=\delta\). No requirement in the resource-envelope argument forces
the cutoff to grow with \(d\).

Indeed, before imposing any capacities, the scalar has the exact form
\[
F_r=\alpha\sum_{t\ge0}H_t+(r-1-\alpha)H_0+cH_1
 +\sum_{t\ge2}\left(\frac{r-1}{t+1}-\alpha\right)H_t.
\]
For \(t\ge n\) the last coefficient is nonpositive. Dropping that tail
and applying the original bounds
\(H_0=d\), \(\sum H_t\le dV\), \(H_t\le M\), and
\(H_1\le M-a\) gives precisely the proposed \(U_r(e,d;n)\).
The capacity for \(H_1\) occurs once. The argument does not assume that
the support of the resource sequence lies below the frozen cutoff.

The finite-sum formula for \(U_r\), its \(e\)-slope \(A_r\), the
triangular-base threshold identity, and the base identity
\(g_0=(a+9)A_0+C\) all agree with the original definitions. I also
verified these as symbolic rational identities, treating \(a,r,n\) as
independent symbols where possible, rather than checking only numerical
instances.

The sign argument for the fixed-cutoff linear coefficient is sound:
\(C<0\) follows from \(n\ge r\), \(a\ge10\); once \(g_0>0\),
\(A_0>-C/(a+9)>0\). The two identities for \(F_0-F_1\) and \(F_1\)
are correct. With \(a=r(r+1)/2\),
\[
\frac{r^2-5r+22}{4}\ge\frac92,\qquad
a+3>4(r-1),
\]
so \(b_0=A_0+11-r-8\alpha>1/4\), as claimed.

For every **integer** \(t=d-a\ge0\), the proposed identities are exact:
\[
A_r(a+t;n)=A_0+t(1-\alpha),
\]
\[
G_r(10,a+t;n)=g_0+t b_0+(1-\alpha)t(t-1)/2.
\]
Their positivity uses \(t(t-1)/2\ge0\) for nonnegative integers. The
affine extension in \(e\) then proves the original sufficient scalar
inequality for every integer \(e\ge10\), \(r\ge4\), \(d\ge a\).
This even includes formal triples with ranks too large to occur as actual
cuts, so imposing the actual-cut restrictions causes no coverage loss.
The original §10 reduction applies to the actual rank without changing
the resource sequence or introducing a maximum-rank envelope.

## 2. Scalar: the elementary rank barrier works

For \(B(r)=r/4+1+9/(2r)\), direct symbolic simplification gives
\[
T_1(r)-B(r)=
\frac{r^3[(r-10)(2r+15)+2]+r[111(r-10)+210]+972}
 {2r(r-1)(r^2+r+6)(r^2+r+18)}.
\]
The denominator and numerator are positive for every real \(r\ge10\).
The parity comparison \(T_1(r)\le T_r\) has the correct direction:
the subtracted numerator is positive and the parity-1 denominator is the
smaller one.

At the new anchor \(r=10\), \(n=28\), convex endpoint interpolation gives
\(H_{28}-H_{23}\le65/336\). The retained strict anchor
\(H_{23}<747/200\), together with the exact positive margin
\(B(10)-747/200-65/336=181/8400\), proves \(H_{28}<B(10)\).

For the rank step, the floor estimates for
\(b=n_{r+1}-n_r\) are correct, including both parities. The interpolation
bound is strictly below \(2/r\), because the displayed difference is
\[
\frac{8(r^2+3r+6)}{r(r^2+r+6)(r^2+3r+4)}>0.
\]
Meanwhile
\[
B(r+1)-B(r)-2/r
=\frac{(r-10)(r+3)+4}{4r(r+1)}>0\quad(r\ge10).
\]
Thus the induction proves \(H_{n_r}<B(r)<T_r\) for all integer
\(r\ge10\). The unchanged six comparisons cover \(4\le r\le9\).
There is no need for the old \(9\to10\) threshold comparison or the
degree-10 rank-difference polynomial.

## 3. Width candidates: all rows and ranges are covered

### First-row replacement

Appendix C (5.1) has exactly the hypotheses needed here: \(Q\) is a
standard graded Artin quotient in \(q\) variables with \(h_0=1\) and
\(h_1=q\). Retaining \(h_2\) and replacing only the \(n\ge3\) weights
by \((q-1)/4\) gives
\[
b_1(Q)\le\frac{q-1}{4}P+\frac{(q+1)^2}{4}
 +\frac{q-1}{12}h_2
\le\frac{q-1}{4}P+\frac{(q+1)(q+2)(q+3)}{24}.
\]
Here \(h_2\le\binom{q+1}{2}\) is valid in every characteristic.
Substitution into the unchanged endpoint inequality
\(\beta_1(G)\le b_1(Q)+P+R\), with \(P\le B\) and \(R\le B-u\),
gives exactly (III), since \(q=e-2\). In particular \(P\) remains the
integer-core quotient length, not the actual quotient length. The
kernel–Tor compensation from Appendix C (3.1)–(3.2) is retained.

The bound \(b(s-b)\le\lfloor s^2/4\rfloor\) uses only the fact that
\(b\) is an integer remainder. All four formulas for \(B_*\) and all
four gap polynomials for \(e=6,7,8,9\) are exact, with strictly positive
constant terms and nonnegative remaining coefficients. Thus they prove
the first row for all \(u=2e-2+z\), \(z\ge0\), without a finite core
enumeration or an unproved monotonicity claim.

For \(e\ge10\), the old coarse bound \(B\le u^2/(e-1)\) suffices.
Identity (V) is correct, and every coefficient is nonnegative on the
stated range. The sparse ranges \(e=6,7,8,9\) and \(e\ge10\) together
cover every \(e\ge6\), \(u\ge2e-2\). The unchanged dense argument
covers the adjacent widths through \(u=2e-3\); no integer width is
omitted. Higher rows continue to use the old \(U_i,T_i\) arguments.

### Five generators at \(u=6,7\)

For \(q=3\), (VI) follows directly from Appendix C (5.1), using
\(h_1=3\). At \(u=6\), (W4) gives \(P\le8,R=0\), and integrality
turns \(b_1\le2P/3+10/3\le26/3\) into \(b_1\le8\). Thus
\(\beta_1\le16=F_1^{\min}(6)\).

At \(u=7\), (W4) gives \(P\le10,R\le3\), and (VI) always gives
\(b_1\le10\). If \(R>0\), (W3) forces \(H_x\ge3\). A minimal
point with first coordinate at least 3 cannot lie in residue 0, whose
only minimal point is \((0,0)\). Its degree is \(L+K+1\ge4\), so
\(\tau=\sum_{n\ge3}h_n\ge1\). The proposed subtraction of
\(\tau/6\) is valid because \(2/(n+1)\le1/2\) for \(n\ge3\).
It yields \(b_1<10\), hence \(b_1\le9\). The cases then give
\(\beta_1\le20\) if \(R=0\), and \(\beta_1\le22\) if \(R>0\),
both within \(F_1^{\min}(7)=22\).

The replacement for the remaining rows also follows from the stated
inputs. The incidence bound gives \(b_1\le P+2\); the degree-0 unit is
not in the socle because \(h_1=3\), so \(b_3\le P-1\). The rank-zero
Euler identity over the three-variable polynomial ring gives
\(b_2=b_1+b_3-1\le2P\). Applying the same endpoint inequality gives
exactly the four displayed upper bounds. The two capacity tables are
correct in every row, including rows 4 and 5.

## 4. Conditions to retain and verification limits

- Keep the scalar domain integer-valued, with \(e\ge10\), \(r\ge4\),
  \(\delta\ge a_r\), and keep the original actual-cut resource bounds.
  Nothing here supports lowering the embedding-dimension threshold.
- In the width argument, keep \(P=P_C\), the actual-source definition of
  \(R\), the kernel correction, and the actual completion capacity.
  No stronger estimate such as \(P+R\le W\) was used.
- At \(e=5,u=7\), retain the conditional \(R>0\) argument. An
  unconditional assertion \(b_1\le9\) is not proved by these inputs.
- Only the specified first-row branches and the two small five-generator
  lex counts can be removed. Dense-width BHP/EK, one-gap arguments,
  higher-row estimates, and the \(e=5,u\ge8\) structural split remain.
- All new divisions occur in rational inequalities between dimensions or
  integer counts, not in the base field. The proposals therefore preserve
  arbitrary-field validity, including finite fields. They introduce no
  generic-coordinate choice or characteristic-dependent rank assumption.

Fresh exact checks run during this review:

```text
python -B simplification_search/scalar/check_scalar_simplifications.py
python -B simplification_search/width/check_width_candidates.py
```

Both exited 0. The scalar check confirmed the seven rational margins, the
new barrier identity, and all 351 advertised finite diagnostics. The width
check confirmed all table and general-gap identities and the two
higher-row capacity comparisons. An additional independent SymPy session
verified the scalar envelope's slope, triangular threshold, base \(C\),
fixed-cutoff quadratic and forward difference, both \(F\) identities,
harmonic-step difference, and barrier identity as symbolic rational
identities. Universal validity follows from the sign and coverage
arguments above; the finite diagnostics are supplemental. This review
does not claim Lean verification or a revalidation of unrelated portions
of the complete proof.
