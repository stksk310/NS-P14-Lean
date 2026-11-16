# Semantic and bibliographic checks

Checked 16 November 2026 against `stksk310/NS-P14-Lean` at
`a5e122a4d09536b1609c5faa8d419f8faf81671f`. Definitions below were fetched through
the GitHub connector at this exact commit; this note records a source inspection,
not a new execution of Lean or a new full audit of every proof dependency.

## Meaning of the final theorem

The conclusion in `NSP14/Main.lean`,
`NumericalSemigroup.p14_totalBetti_le_intervalCompletion`, is the intended
inequality for the actual completed tangent cones over their separate minimal
polynomial rings. It has no width, embedding-dimension, characteristic,
Cohen--Macaulay, or positive-row hypothesis.

* `NumericalSemigroup` in `Semigroup/Basic.lean` is a cofinite additive submonoid
  of the natural numbers, with a conductor witness which need not be least.
  Its multiplicity is constructed as its least positive element.
* `IsAtom`, `atoms`, `closure_atoms`, and `atom_mem_of_generates` in
  `Semigroup/Atoms.lean` identify the actual positive indecomposables, prove
  finiteness and generation, and prove that every generating set contains them.
  Thus they are precisely the usual unique minimal generators.
* `AtomExponent` in `Homological/Presentation.lean` is the subtype of actual
  semigroup elements that are atoms, and `FullPolynomialRing k` is
  `MvPolynomial S.AtomExponent k`. `atomExponent_card` identifies its variable
  count with the embedding dimension. The variable-to-cone map sends each atom
  to its initial monomial. It is surjective; the atom initial forms are linearly
  independent, and `fullPolynomialToG_linearForm_eq_zero_iff` proves the absence
  of linear relations. This is a minimal homogeneous presentation, not a padded
  presentation on every integer in the interval.
* `FormalSemigroupRing k` in `Semigroup/FormalSemigroupRing.lean` is literally the
  subalgebra of `PowerSeries k` whose coefficients outside the carrier vanish.
  Its distinguished maximal ideal is the kernel of the constant-coefficient map;
  maximality over a field is proved using surjectivity onto that field.
* `FormalGradedPiece k n` in `Semigroup/FormalTangentAlgebra.lean` is the quotient
  of the actual ideal power by the next power. `FormalTangentAlgebra` is their
  direct sum, with multiplication induced from multiplication of representatives.
  Consequently it is precisely `gr_m k[[t^S]]`, not an abstract vector space
  assigned a desired Hilbert function.
* `formalOrderIdeal_eq_pow` and `mem_formalMaximalIdeal_pow` in
  `Semigroup/FormalFactorization.lean` prove the support/order description for
  infinite series by an explicit finite factorization. `order` is the maximal
  positive-element decomposition length; `order_realized_by_atoms` in
  `Semigroup/Order.lean` identifies it with maximal minimal-generator length.
* `completedGradedAlgEquiv` in `Semigroup/CompletedComparison.lean` is a
  multiplicative, degree-preserving algebra equivalence from the algebraic
  semigroup-ring tangent cone to the completed one, and preserves atom initial
  forms. `completedPolynomialLinearEquiv` in `Homological/Presentation.lean`
  preserves the full polynomial action. The module structure used in the public
  theorem is this action.

## Betti numbers are ordinary Tor dimensions

`totalBetti` in `Homological/Betti.lean` is the natural-number `finrank` over the
given coefficient field of `koszulHomologyK`, with all variables in the specified
finite variable type. The following checks rule out the usual semantic loopholes:

1. `variableList` in `Homological/KoszulResolution.lean` contains each variable
   exactly once. `residueField` is the actual coefficient field with the
   polynomial action given by evaluation of all variables at zero.
2. `koszulResolution` is a `ProjectiveResolution` of that residue module, proved
   using polynomial-variable exactness and the augmentation. `tensorKoszulIso`
   and `torKoszulIso` in `Homological/KoszulTor.lean` identify the actual tensor
   complex with ordinary mathlib `CategoryTheory.Tor`, derived in its second
   factor. `torCoefficientIso` restricts the resulting Tor module to the
   coefficient field. Thus the number is
   `dim_k Tor_i^{k[X_a : a atom]}(G_S,k)`.
3. An infinite-dimensional module can have misleading natural-number `finrank`
   in Lean, but this case is explicitly excluded mathematically here:
   `koszul_homology_finite` in `Homological/KoszulAnnihilation.lean` proves finite
   dimension over `k` for every finitely generated polynomial module. It first
   proves finite generation of homology over the polynomial ring and then proves
   that every variable annihilates it. The two cone modules are finitely generated:
   `fullPolynomialGFinite` follows from the quotient map and
   `formalGFullPolynomialFinite` in `Homological/ActualTorTransport.lean` follows
   through the actual polynomial-linear completion equivalence.
4. `completedTorIso` transports ordinary Tor over the same full polynomial ring;
   `completed_totalBetti` gives the equality consumed by final assembly.

No vacuous extra assumption was found in the final statement or these semantic
connections. This finding is narrower than an independent kernel rebuild or a
line-by-line re-verification of all branch proofs.

## The target and boundary rows

`intervalCompletionAll` in `Semigroup/IntervalCompletionAll.lean` has carrier
exactly `AddSubmonoid.closure (Set.Icc S.multiplicity S.maxAtom)`. Its conductor
witness is inherited from the source, using containment of the source in this
literal closure; no comparison inequality occurs in its definition.

For embedding dimension at least two, `intervalCompletion_embeddingDimension`
in `Semigroup/IntervalCompletion.lean` gives
`min(width,multiplicity-1)+1`. Consequently, with
`v=min(M-m,m-1)`, the target minimal generators are `m,...,m+v`.
`Main/IntervalTarget.lean` transports Betti numbers when two structures have the
same carrier without equating their possibly different conductor witnesses.
The source and target each retain their own `AtomExponent` type. In embedding
dimension one the source is the natural numbers and completion is literally
generated by `[1,1]`.

The public theorem includes row zero and arbitrarily high rows. It does not
claim that target rows vanish above the source embedding dimension.
`tests/MainBoundaryRows.lean` contains the useful check
`S=<6,7,9,11>`: the source fifth Betti number is zero, whereas the completion
`<6,7,8,9,10,11>` has fifth Betti number five, over every field.

## Provenance of Problem 14

The precise problem-number source is Moscariello--Sammartano,
[*Open problems on relations of numerical semigroups*, arXiv:2406.00790v1,
Section 3, Problem 14](https://arxiv.org/html/2406.00790v1#S3): it asks the
all-row tangent-cone interval comparison. The survey later appeared as a
[Springer chapter](https://doi.org/10.1007/978-3-031-75326-8_16), pages 365--380
in volume 477 of *Springer Proceedings in Mathematics & Statistics* (2025).
The bibliography uses the verified published metadata and records the version
where the problem was checked.

Herzog--Stamate's [Conjecture 2.4 in arXiv:1308.4644v3](https://arxiv.org/pdf/1308.4644v3)
only states the minimal-generator comparison for the defining ideals. Higher
Betti numbers are suggested around Proposition 2.10, where they are proved for
arithmetic sequences. Lan--Tu--Vu explicitly note this distinction in Remark 5.3
of [their version 1](https://arxiv.org/html/2307.05589v1). Therefore the paper
should say it resolves Problem 14 / the higher-Betti interval-completion problem,
and should not identify the full statement verbatim with HS Conjecture 2.4.

## Citation contracts

The entries in `references.bib` include only fields checked in primary arXiv,
publisher, or author-hosted sources. An arXiv-only entry is deliberate where a
published record was unnecessary to establish the exact version and numbering.

| Key | Exact input and checked location | Convention or limitation |
| --- | --- | --- |
| `ProblemList` | Moscariello--Sammartano, arXiv:2406.00790v1, Section 3, Problem 14 | Quotient-ring Betti convention matches the theorem. |
| `APFormula` | Gimenez--Sengupta--Srinivasan, arXiv:1108.3203v1, Theorem 4.1 and equation (4.1) | Minimal arithmetic sequence, coprime generators, arbitrary coefficient field. The formula already gives quotient-ring Betti numbers; no homological index shift is needed. |
| `APCone` | Herzog--Stamate, arXiv:1308.4644v3, Proposition 2.5 | Equality for ideals is converted to equality for quotient rings by shifting positive homological indices. |
| `LanTuVu` | Lan--Tu--Vu, arXiv:2307.05589v1, Theorem 1.1, final sentence | Three minimal generators; arbitrary field. Their ideals use index one lower than quotient rings. Their stronger explicit bounds need not be claimed as formalized inputs. |
| `GreenRestriction` | Caviglia, arXiv:2104.11836v1, Section 1, equation (1.1) | Infinite field, any characteristic. Only its degree-two specialization is used; field extension/descent handles finite fields. |
| `BHP` | Juhnke-Kubitzke--Venturello, Section 2.2, Lemma 2 | Verified modern reprint of lex Betti domination, including positive characteristic. The key denotes this reprint, not a single original BHP paper. |
| `EK` | Eliahou--Kervaire; formula reprinted in Juhnke-Kubitzke--Venturello, Section 2.2, Lemma 3 | Strongly stable (in particular lex) monomial ideal. Convert ideal index to quotient index. |
| `Kneser` | DeVos, arXiv:1303.3539v1, Theorem 1 | Finite nonempty subsets of an abelian group; the stabilizer form allows composite cyclic group order. |
| `SavchevChen` | Savchev--Chen, arXiv:math/0602568v1, Section 4, Theorem 8 | Zero-sum-free sequence of length strictly greater than half the cyclic group order; a unit makes the sum of least positive representatives less than the order. |

The theorem and lemma source locations above were checked against the stated
versions, rather than inferred from the informal source table alone.

Two bibliographic/convention corrections should be retained when writing:
the GSS formula already concerns the quotient ring (the informal Japanese
chapter's blanket instruction to shift from an ideal resolution is unnecessary
there), and its published volume is **388** (2013), not the **338** misprinted in
the LTV reference list. The bibliography uses the verified publisher volume and
DOI. The EK original metadata is checked through the primary Juhnke-Kubitzke--
Venturello bibliography; the formula itself was checked in their Lemma 3.
