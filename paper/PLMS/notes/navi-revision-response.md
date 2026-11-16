# Response to Navi's manuscript audit — revision 2

All five requested changes were checked and implemented. The original
22-page bundle is preserved as `P14_English_Manuscript_Draft_2026-11-16.zip`.

## Sharp width corollary and prior work

Added Caviglia–Moscariello–Sammartano, *Bounds for syzygies of monomial curves*,
Proc. Amer. Math. Soc. **152** (2024), 3665–3678,
[DOI 10.1090/proc/16862](https://doi.org/10.1090/proc/16862).
The statement was checked in
[arXiv:2307.05770v2, Conjecture 1.3](https://arxiv.org/html/2307.05770v2).
It concerns positive homological degrees of the local semigroup ring,
computed over its minimal formal-power-series presentation.

The new corollary states the bound for every S, every field and every i≥1,
and gives a simultaneous equality family at each positive width. Its proof
uses the standard filtered-Koszul comparison, the unchanged interval theorem,
and the exact target formula. For i≤D the correction is at most
`(v+1−i) C(v,i−1) = i C(v,i)`; for i>D it is also at most `i C(v,i)`.
Pascal and v≤w give the bound. Width zero is handled separately, and AP
semigroup/cone Betti equality proves sharpness for the ordinary family.

The abstract and introduction mention the consequence. The appendix
distinguishes the Lean theorem about tangent cones from the standard local-ring
comparison used for the corollary. No new Lean declaration for the local-ring
corollary or fresh full Lean replay is claimed.

## One-hole quantifiers

Confirmed the reported q=3,r=0,s=3,i=1 counterexample: T_i=4 but
C(q+2,i−1)=1. Both binomial bounds now explicitly require interior holes
r,s≥1. The end-hole paragraph explicitly avoids them and retains its
separate delta=1 compensation identity. The main theorem is unchanged.

## Harmonic estimate and zeroth homology

Expanded the initial-module argument with augmented module-monomial labels,
the divisor-closed standard basis, triangular normal-form action, and
diagonal-block minors. The boundary-rank direction is now explicit.
Checked against the pinned `Homological/InitialModule.lean`,
`Homological/KoszulStandardMinor.lean`, and `Homological/StandardHarmonic.lean`.
The same-degree multi-generator interface and arbitrary characteristic remain.

The full-variable transfer now explains that relative H0 has dimension q but
carries the nontrivial remaining-variable action of `k[Z]/(Z)^2`. Its
contribution is T_q, rather than `q(1+z)^(q−1)`. Subtracting q removes
it before the positive relative rows are estimated, preventing double counting
and keeping the zeroth Betti number equal to 1. The formula itself is unchanged.

## Pardue reference

Added Keith Pardue, *Deformation classes of graded modules and maximal Betti
numbers*, Illinois J. Math. **40** (1996), no. 4, 564–585,
[DOI 10.1215/ijm/1255985937](https://doi.org/10.1215/ijm/1255985937),
and cited Theorem 31 in the lex comparison. Its arbitrary-characteristic
application is explicitly confirmed in the proof of CMS Theorem 2.1.
The original Project Euclid endpoint returned a service/security page, so
this revision does not claim a new full reading of Pardue's original proof.
The direct citation and the existing modern-source citation are both retained.

## Fresh checks and scope

- Exact target upper envelope: 348,450 tuples with 1≤v≤100,
  1≤D≤v, 1≤i≤v+2, including rows beyond the target; PASS.
- Interior-hole inequalities: 45,320 tuples with 3≤q≤50; PASS.
- Both end-hole identities in the same ranges: PASS; counterexample 4>1 reproduced.
- The manuscript gives general algebraic proofs; finite checks are supplementary.
- The revised PDF builds successfully with latexmk and has 23 pages.
  Final reference/layout/hash checks are recorded in `DRAFT_VALIDATION.json`.

This is an editing response, not a new independent referee report.
The original independent review remains historical evidence for its own scope.
