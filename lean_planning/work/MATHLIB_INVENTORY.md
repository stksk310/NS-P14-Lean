# Mathlib source inventory for NS-P14 planning

Audit date: 2026-11-09T12:33:47.904462+00:00. Public mathlib commit **`139105d28c7685a154cb3093f79edb2e16708099`** (commit timestamp `2026-11-09T10:33:51Z`).
Pinned [lean-toolchain](https://github.com/leanprover-community/mathlib4/blob/139105d28c7685a154cb3093f79edb2e16708099/lean-toolchain): **`leanprover/lean4:v4.36.0-rc2`**. This is a current HEAD snapshot, not a claim that a released stable package supplies the same APIs.

**Scope and evidence standard.** PLANONLY source audit of all 8,691 `Mathlib/**/*.lean` filenames/content with targeted searches and representative source reads. The public checkout is under `/tmp/ns-p14-mathlib-audit`; no Lean project or toolchain was installed. `lean`, `lake`, and `elan` were unavailable, and no compilation/elaboration was attempted. “Verified” below means source declarations and representative statements/proof bodies were inspected at the pinned commit. It does not mean a prospective NS-P14 import or proposed application compiled.

**Absence language.** “Not found” is a bounded lexical/source-review result. It is not a proof that no equivalent theorem exists under another name. No item is classified “definitely absent”. Exact search patterns, all matching lines, evidence snippets and file SHA-256 values are in [mathlib_inventory.json](mathlib_inventory.json).

## Findings that materially change the estimate

- Numerical-semigroup groundwork is partly reusable: `Nat.exists_mem_closure_of_ge` proves eventual membership of gcd multiples and `Nat.addSubmonoid_fg` proves finite generation. The paper’s Apéry/order/tangent-cone interfaces remain new domain work.
- The Rees quotient supplies a promising associated-graded construction route. It already has the extended-ideal coefficient characterization `a_n ∈ I^(n+1)` and Noetherian quotient results. An explicit graded-piece/tangent-cone equivalence remains to be proved.
- General homological foundations are substantial: projective resolutions, Ext, concrete kernel/image homology, long exact homology, total complexes and abstract spectral sequences exist. Calling all homological algebra missing would overestimate work.
- The paper-facing commutative-homological bridge is the gap: no algebraic Koszul complex/API or ready-made Betti/Koszul/Tor comparison was found. The categorical `Tor.lean` itself explicitly records limited scope. A concrete finite Koszul homology route can avoid building a full graded minimal-resolution API, while retaining an explicit obligation to identify the intended Betti numbers.
- The precise published inputs (Kneser, Savchev–Chen, Green, BHP/EK, AP Betti and cone equality, LTV) were not found by the recorded audit. Generic foundations do not discharge these inputs.

## NS: Numerical semigroups, finite generation, cofiniteness, Apéry

**Status:** `foundations_verified_exact_apery_api_not_found`.

**Verified reuse.** AddSubmonoid.closure is already used for nonnegative generated semigroups. Eventual membership of gcd multiples and finite generation of every additive submonoid of N are proved. The two-generator Frobenius formula is also in this file.

| Declaration or source item | Pinned evidence |
|---|---|
| `FrobeniusNumber` | [Mathlib/NumberTheory/FrobeniusNumber.lean:48](https://github.com/leanprover-community/mathlib4/blob/139105d28c7685a154cb3093f79edb2e16708099/Mathlib/NumberTheory/FrobeniusNumber.lean#L48) |
| `Nat.exists_mem_closure_of_ge` | [Mathlib/NumberTheory/FrobeniusNumber.lean:171](https://github.com/leanprover-community/mathlib4/blob/139105d28c7685a154cb3093f79edb2e16708099/Mathlib/NumberTheory/FrobeniusNumber.lean#L171) |
| `Nat.addSubmonoid_fg` | [Mathlib/NumberTheory/FrobeniusNumber.lean:196](https://github.com/leanprover-community/mathlib4/blob/139105d28c7685a154cb3093f79edb2e16708099/Mathlib/NumberTheory/FrobeniusNumber.lean#L196) |
| `exists_frobeniusNumber_iff` | [Mathlib/NumberTheory/FrobeniusNumber.lean:208](https://github.com/leanprover-community/mathlib4/blob/139105d28c7685a154cb3093f79edb2e16708099/Mathlib/NumberTheory/FrobeniusNumber.lean#L208) |

**New or unverified bridge.** No exact NumericalSemigroup or Apéry API found by the recorded targeted scans. Need project definitions of multiplicity, atoms/minimal generators, Apéry representatives, longest representation order, and their interface to actual tangent cone.

**Planning consequence.** Do not budget gcd/cofiniteness foundations as wholly new; do budget the Apéry/order/atom and actual-quotient bridge as new substantial domain work.

## SEMIRING: Semigroup algebra and power-series/completion foundations

**Status:** `foundations_verified`.

**Verified reuse.** Finite-support additive monoid algebras and general ideal-adic completion exist; power-series and Hahn-series directories are present.

| Declaration or source item | Pinned evidence |
|---|---|
| `AddMonoidAlgebra` | [Mathlib/Algebra/MonoidAlgebra/Defs.lean:64](https://github.com/leanprover-community/mathlib4/blob/139105d28c7685a154cb3093f79edb2e16708099/Mathlib/Algebra/MonoidAlgebra/Defs.lean#L64) |
| `AdicCompletion` | [Mathlib/RingTheory/AdicCompletion/Basic.lean:172](https://github.com/leanprover-community/mathlib4/blob/139105d28c7685a154cb3093f79edb2e16708099/Mathlib/RingTheory/AdicCompletion/Basic.lean#L172) |

**New or unverified bridge.** No verified ready-made k[[t^Gamma]] construction or identification of its associated graded ring with the paper finite monomial model. Algebraic semigroup ring plus adic completion may be a route, but equivalence has to be proved.

**Planning consequence.** Prefer proving the finite monomial tangent model interface once. Replacing the actual ring by a convenient model without an equivalence theorem would weaken the target.

## FILT: Adic filtrations

**Status:** `verified`.

**Verified reuse.** Descending I-filtrations, stable I-filtrations, Rees module finite-generation criterion, and Artin-Rees are implemented.

| Declaration or source item | Pinned evidence |
|---|---|
| `Ideal.Filtration` | [Mathlib/RingTheory/Filtration.lean:52](https://github.com/leanprover-community/mathlib4/blob/139105d28c7685a154cb3093f79edb2e16708099/Mathlib/RingTheory/Filtration.lean#L52) |
| `Ideal.stableFiltration` | [Mathlib/RingTheory/Filtration.lean:178](https://github.com/leanprover-community/mathlib4/blob/139105d28c7685a154cb3093f79edb2e16708099/Mathlib/RingTheory/Filtration.lean#L178) |
| `Ideal.Filtration.submodule_fg_iff_stable` | [Mathlib/RingTheory/Filtration.lean:336](https://github.com/leanprover-community/mathlib4/blob/139105d28c7685a154cb3093f79edb2e16708099/Mathlib/RingTheory/Filtration.lean#L336) |
| `Ideal.exists_pow_inf_eq_pow_smul` | [Mathlib/RingTheory/Filtration.lean:388](https://github.com/leanprover-community/mathlib4/blob/139105d28c7685a154cb3093f79edb2e16708099/Mathlib/RingTheory/Filtration.lean#L388) |

**New or unverified bridge.** F.submodule in this file is the direct sum of the N_i embedded in M[X], not the quotient direct sum N_i/N_(i+1). It must not be advertised as an associated graded module implementation.

**Planning consequence.** Large reuse for filtration and finite-generation lemmas; the project still needs the successive-quotient construction/interface.

## REES: Rees algebra and associated-graded route

**Status:** `rees_verified_associated_graded_bridge_unverified`.

**Verified reuse.** Rees algebra is coefficientwise I^n in R[X]; generated in degree one; FG of I gives FG of Rees. Noetherian R gives finite type then Noetherian Rees. More generally Noetherian R/I and FG I give a Noetherian Rees quotient. Its extended-I ideal is characterized by coefficient n belonging to I^(n+1).

| Declaration or source item | Pinned evidence |
|---|---|
| `reesAlgebra` | [Mathlib/RingTheory/ReesAlgebra.lean:39](https://github.com/leanprover-community/mathlib4/blob/139105d28c7685a154cb3093f79edb2e16708099/Mathlib/RingTheory/ReesAlgebra.lean#L39) |
| `adjoin_monomial_eq_reesAlgebra` | [Mathlib/RingTheory/ReesAlgebra.lean:101](https://github.com/leanprover-community/mathlib4/blob/139105d28c7685a154cb3093f79edb2e16708099/Mathlib/RingTheory/ReesAlgebra.lean#L101) |
| `reesAlgebra.fg` | [Mathlib/RingTheory/ReesAlgebra.lean:115](https://github.com/leanprover-community/mathlib4/blob/139105d28c7685a154cb3093f79edb2e16708099/Mathlib/RingTheory/ReesAlgebra.lean#L115) |
| `anonymous Algebra.FiniteType instance` | [Mathlib/RingTheory/ReesAlgebra.lean:127](https://github.com/leanprover-community/mathlib4/blob/139105d28c7685a154cb3093f79edb2e16708099/Mathlib/RingTheory/ReesAlgebra.lean#L127) |
| `anonymous IsNoetherianRing instance` | [Mathlib/RingTheory/ReesAlgebra.lean:130](https://github.com/leanprover-community/mathlib4/blob/139105d28c7685a154cb3093f79edb2e16708099/Mathlib/RingTheory/ReesAlgebra.lean#L130) |
| `tensorProduct_reesAlgebra_isNoetherian_of_fg` | [Mathlib/RingTheory/ReesAlgebra.lean:134](https://github.com/leanprover-community/mathlib4/blob/139105d28c7685a154cb3093f79edb2e16708099/Mathlib/RingTheory/ReesAlgebra.lean#L134) |
| `isNoetherianRing_reesAlgebra_quotient` | [Mathlib/RingTheory/ReesAlgebra.lean:140](https://github.com/leanprover-community/mathlib4/blob/139105d28c7685a154cb3093f79edb2e16708099/Mathlib/RingTheory/ReesAlgebra.lean#L140) |
| `mem_map_algebraMap_reesAlgebra_iff` | [Mathlib/RingTheory/ReesAlgebra.lean:146](https://github.com/leanprover-community/mathlib4/blob/139105d28c7685a154cb3093f79edb2e16708099/Mathlib/RingTheory/ReesAlgebra.lean#L146) |

**New or unverified bridge.** No named associated-graded ring/filtration construction found in targeted searches. The existing quotient of Rees by extended I is a credible definition candidate; the graded-piece identification with I^n/I^(n+1) and paper tangent-cone equivalence are not verified reusable theorems.

**Planning consequence.** This is a significant reuse opportunity, reducing construction and Noetherian overhead without eliminating graded-piece and actual-semigroup model proofs.

## GRADED: Graded rings and modules

**Status:** `verified`.

**Verified reuse.** Internal direct-sum decompositions, graded scalar action, external graded module and induced module structures exist.

| Declaration or source item | Pinned evidence |
|---|---|
| `GradedRing` | [Mathlib/RingTheory/GradedAlgebra/Basic.lean:65](https://github.com/leanprover-community/mathlib4/blob/139105d28c7685a154cb3093f79edb2e16708099/Mathlib/RingTheory/GradedAlgebra/Basic.lean#L65) |
| `DirectSum.decomposeAlgEquiv` | [Mathlib/RingTheory/GradedAlgebra/Basic.lean:198](https://github.com/leanprover-community/mathlib4/blob/139105d28c7685a154cb3093f79edb2e16708099/Mathlib/RingTheory/GradedAlgebra/Basic.lean#L198) |
| `DirectSum.Gmodule` | [Mathlib/Algebra/Module/GradedModule.lean:44](https://github.com/leanprover-community/mathlib4/blob/139105d28c7685a154cb3093f79edb2e16708099/Mathlib/Algebra/Module/GradedModule.lean#L44) |
| `DirectSum.Gmodule.module` | [Mathlib/Algebra/Module/GradedModule.lean:138](https://github.com/leanprover-community/mathlib4/blob/139105d28c7685a154cb3093f79edb2e16708099/Mathlib/Algebra/Module/GradedModule.lean#L138) |

**New or unverified bridge.** No exact graded minimal free resolution / graded Betti API found. Graded module basics do not imply such an API.

**Planning consequence.** Use existing grading structures where useful. For total Betti inequalities, a concrete finite Koszul model could avoid developing a full category of graded minimal resolutions.

## RES: Free/projective resolutions and polynomial finite-resolution bound

**Status:** `abstract_foundations_verified_exact_minimal_or_hilbert_syzygy_not_found`.

**Verified reuse.** ModuleCat has a functorial projective cover built from free modules; generic projective-resolution comparison and left-derived functors are available.

| Declaration or source item | Pinned evidence |
|---|---|
| `ModuleCat.projectiveResolution` | [Mathlib/Algebra/Category/ModuleCat/LeftResolution.lean:42](https://github.com/leanprover-community/mathlib4/blob/139105d28c7685a154cb3093f79edb2e16708099/Mathlib/Algebra/Category/ModuleCat/LeftResolution.lean#L42) |
| `CategoryTheory.ProjectiveResolution.lift` | [Mathlib/CategoryTheory/Abelian/Projective/Resolution.lean:92](https://github.com/leanprover-community/mathlib4/blob/139105d28c7685a154cb3093f79edb2e16708099/Mathlib/CategoryTheory/Abelian/Projective/Resolution.lean#L92) |
| `CategoryTheory.ProjectiveResolution.homotopyEquiv` | [Mathlib/CategoryTheory/Abelian/Projective/Resolution.lean:180](https://github.com/leanprover-community/mathlib4/blob/139105d28c7685a154cb3093f79edb2e16708099/Mathlib/CategoryTheory/Abelian/Projective/Resolution.lean#L180) |
| `CategoryTheory.Functor.leftDerivedToHomotopyCategory` | [Mathlib/CategoryTheory/Abelian/LeftDerived.lean:64](https://github.com/leanprover-community/mathlib4/blob/139105d28c7685a154cb3093f79edb2e16708099/Mathlib/CategoryTheory/Abelian/LeftDerived.lean#L64) |

**New or unverified bridge.** Finite ranks, minimality, grading, finite polynomial-ring resolution length (Hilbert syzygy), and rank=Betti characterizations were not found as exact reusable results in the recorded scans. These functorial free covers can be infinitely generated.

**Planning consequence.** Do not label all resolutions absent; equally do not assume generic projective resolutions deliver the paper finite minimal free resolutions. Concrete Koszul Betti definitions avoid some, but not all, comparison obligations.

## TOR: Tor and its paper-facing API

**Status:** `definition_and_projective_vanishing_verified`.

**Verified reuse.** Tor is a categorical left-derived tensor functor; projective higher vanishing is proved. Flat tensoring preserves exactness in ModuleCat.

| Declaration or source item | Pinned evidence |
|---|---|
| `CategoryTheory.Tor` | [Mathlib/CategoryTheory/Monoidal/Tor.lean:44](https://github.com/leanprover-community/mathlib4/blob/139105d28c7685a154cb3093f79edb2e16708099/Mathlib/CategoryTheory/Monoidal/Tor.lean#L44) |
| `CategoryTheory.Tor'` | [Mathlib/CategoryTheory/Monoidal/Tor.lean:50](https://github.com/leanprover-community/mathlib4/blob/139105d28c7685a154cb3093f79edb2e16708099/Mathlib/CategoryTheory/Monoidal/Tor.lean#L50) |
| `CategoryTheory.isZero_Tor_succ_of_projective` | [Mathlib/CategoryTheory/Monoidal/Tor.lean:56](https://github.com/leanprover-community/mathlib4/blob/139105d28c7685a154cb3093f79edb2e16708099/Mathlib/CategoryTheory/Monoidal/Tor.lean#L56) |
| `Module.Flat.lTensor_shortComplex_exact` | [Mathlib/RingTheory/Flat/CategoryTheory.lean:41](https://github.com/leanprover-community/mathlib4/blob/139105d28c7685a154cb3093f79edb2e16708099/Mathlib/RingTheory/Flat/CategoryTheory.lean#L41) |

**New or unverified bridge.** Tor.lean documentation says the Tor/Tor' comparison remains future work. Flat/CategoryTheory.lean TODO says relate flatness with Tor. A concrete polynomial Koszul computation, balancedness, finite-dimensionality, long exact Tor sequence and flat base-change Betti equality are not verified ready-made in this audit.

**Planning consequence.** Use concrete Koszul homology for project-facing Betti estimates if approved in the design; still prove its agreement with the intended mathematical Betti numbers. General Tor APIs may require more infrastructure than the project needs.

## EXT: Ext foundations and finite generation

**Status:** `verified`.

**Verified reuse.** Ext over ModuleCat, dimension shifting, and finite generation of Ext between finite modules over a Noetherian ring are implemented.

| Declaration or source item | Pinned evidence |
|---|---|
| `ModuleCat.finite_ext` | [Mathlib/Algebra/Category/ModuleCat/Ext/Finite.lean:25](https://github.com/leanprover-community/mathlib4/blob/139105d28c7685a154cb3093f79edb2e16708099/Mathlib/Algebra/Category/ModuleCat/Ext/Finite.lean#L25) |
| `ModuleCat.projectiveShortComplex` | [Mathlib/Algebra/Category/ModuleCat/Ext/DimensionShifting.lean:33](https://github.com/leanprover-community/mathlib4/blob/139105d28c7685a154cb3093f79edb2e16708099/Mathlib/Algebra/Category/ModuleCat/Ext/DimensionShifting.lean#L33) |
| `precomp_extClass_surjective_of_projective_X₂` | [Mathlib/Algebra/Category/ModuleCat/Ext/DimensionShifting.lean:50](https://github.com/leanprover-community/mathlib4/blob/139105d28c7685a154cb3093f79edb2e16708099/Mathlib/Algebra/Category/ModuleCat/Ext/DimensionShifting.lean#L50) |

**New or unverified bridge.** These are not automatically Tor finite-dimensionality or Betti formulas. No exact project bridge was checked.

**Planning consequence.** Substantial abstract homological library exists, but its cost savings should be assigned only to statements actually matching project obligations.

## KOSZUL: Algebraic Koszul complex and its computation of Tor

**Status:** `exact_implementation_not_found`.

**Verified reuse.** Exterior powers and their bases indexed by n-element subsets exist, alongside regular sequences and general chain-complex/homology foundations.

| Declaration or source item | Pinned evidence |
|---|---|
| `Module.Basis.exteriorPower` | [Mathlib/LinearAlgebra/ExteriorPower/Basis.lean:95](https://github.com/leanprover-community/mathlib4/blob/139105d28c7685a154cb3093f79edb2e16708099/Mathlib/LinearAlgebra/ExteriorPower/Basis.lean#L95) |
| `documentation: Koszul regular-sequence TODO` | [Mathlib/RingTheory/Regular/RegularSequence.lean:22](https://github.com/leanprover-community/mathlib4/blob/139105d28c7685a154cb3093f79edb2e16708099/Mathlib/RingTheory/Regular/RegularSequence.lean#L22) |
| `documentation: Koszul-homology characterization future work` | [Mathlib/Algebra/Homology/LocalCohomology.lean:43](https://github.com/leanprover-community/mathlib4/blob/139105d28c7685a154cb3093f79edb2e16708099/Mathlib/Algebra/Homology/LocalCohomology.lean#L43) |

**New or unverified bridge.** Global Koszul scan gave only future-work algebraic mentions and differential-geometric Koszul formulas. No algebraic Koszul complex, its differential square-zero proof, regular-sequence acyclicity, or computation-of-Tor theorem was found.

**Planning consequence.** Treat concrete Koszul construction, exactness/regular-sequence bridge, naturality, tensor/change-of-variable behavior, and Betti identification as substantial new work. Existing exterior bases help with binomial dimensions and explicit coordinate arguments.

## CHAIN: Concrete homology, exact sequence and rank foundations

**Status:** `verified`.

**Verified reuse.** ModuleCat homology identifies with ker/outgoing modulo range/incoming; long exact homology of short exact complexes exists. Rank-nullity and quotient dimension are proved.

| Declaration or source item | Pinned evidence |
|---|---|
| `CategoryTheory.ShortComplex.moduleCatLeftHomologyData` | [Mathlib/Algebra/Homology/ShortComplex/ModuleCat.lean:101](https://github.com/leanprover-community/mathlib4/blob/139105d28c7685a154cb3093f79edb2e16708099/Mathlib/Algebra/Homology/ShortComplex/ModuleCat.lean#L101) |
| `CategoryTheory.ShortComplex.moduleCatHomologyIso` | [Mathlib/Algebra/Homology/ShortComplex/ModuleCat.lean:172](https://github.com/leanprover-community/mathlib4/blob/139105d28c7685a154cb3093f79edb2e16708099/Mathlib/Algebra/Homology/ShortComplex/ModuleCat.lean#L172) |
| `CategoryTheory.ShortComplex.ShortExact.δ` | [Mathlib/Algebra/Homology/HomologySequence.lean:282](https://github.com/leanprover-community/mathlib4/blob/139105d28c7685a154cb3093f79edb2e16708099/Mathlib/Algebra/Homology/HomologySequence.lean#L282) |
| `CategoryTheory.ShortComplex.ShortExact.homology_exact₁` | [Mathlib/Algebra/Homology/HomologySequence.lean:293](https://github.com/leanprover-community/mathlib4/blob/139105d28c7685a154cb3093f79edb2e16708099/Mathlib/Algebra/Homology/HomologySequence.lean#L293) |
| `CategoryTheory.ShortComplex.ShortExact.homology_exact₂` | [Mathlib/Algebra/Homology/HomologySequence.lean:299](https://github.com/leanprover-community/mathlib4/blob/139105d28c7685a154cb3093f79edb2e16708099/Mathlib/Algebra/Homology/HomologySequence.lean#L299) |
| `CategoryTheory.ShortComplex.ShortExact.homology_exact₃` | [Mathlib/Algebra/Homology/HomologySequence.lean:314](https://github.com/leanprover-community/mathlib4/blob/139105d28c7685a154cb3093f79edb2e16708099/Mathlib/Algebra/Homology/HomologySequence.lean#L314) |
| `Submodule.finrank_quotient_add_finrank` | [Mathlib/LinearAlgebra/Dimension/RankNullity.lean:244](https://github.com/leanprover-community/mathlib4/blob/139105d28c7685a154cb3093f79edb2e16708099/Mathlib/LinearAlgebra/Dimension/RankNullity.lean#L244) |
| `LinearMap.finrank_range_add_finrank_ker` | [Mathlib/LinearAlgebra/FiniteDimensional/Lemmas.lean:173](https://github.com/leanprover-community/mathlib4/blob/139105d28c7685a154cb3093f79edb2e16708099/Mathlib/LinearAlgebra/FiniteDimensional/Lemmas.lean#L173) |

**New or unverified bridge.** Need instantiate to the chosen finite Koszul complexes, show finite-dimensionality before using finrank, and derive project-specific rank inequalities. finrank has a zero junk value outside finite rank; a bare definition is insufficient.

**Planning consequence.** Concrete chain-level Betti route can reuse robust homology/exactness/dimension machinery. It is not necessary to rebuild long exact homology or linear-algebra rank-nullity.

## SPECTRAL: Bicomplex, total complex, and spectral sequences

**Status:** `abstract_foundations_verified_application_unverified`.

**Verified reuse.** Bicomplexes, signed total complexes, spectral-sequence pages, and construction from spectral objects including first-quadrant homological variants exist.

| Declaration or source item | Pinned evidence |
|---|---|
| `HomologicalComplex₂` | [Mathlib/Algebra/Homology/HomologicalBicomplex.lean:38](https://github.com/leanprover-community/mathlib4/blob/139105d28c7685a154cb3093f79edb2e16708099/Mathlib/Algebra/Homology/HomologicalBicomplex.lean#L38) |
| `HomologicalComplex₂.total` | [Mathlib/Algebra/Homology/TotalComplex.lean:266](https://github.com/leanprover-community/mathlib4/blob/139105d28c7685a154cb3093f79edb2e16708099/Mathlib/Algebra/Homology/TotalComplex.lean#L266) |
| `CategoryTheory.SpectralSequence` | [Mathlib/Algebra/Homology/SpectralSequence/Basic.lean:36](https://github.com/leanprover-community/mathlib4/blob/139105d28c7685a154cb3093f79edb2e16708099/Mathlib/Algebra/Homology/SpectralSequence/Basic.lean#L36) |
| `CategoryTheory.Abelian.SpectralObject.spectralSequence` | [Mathlib/Algebra/Homology/SpectralObject/SpectralSequence.lean:479](https://github.com/leanprover-community/mathlib4/blob/139105d28c7685a154cb3093f79edb2e16708099/Mathlib/Algebra/Homology/SpectralObject/SpectralSequence.lean#L479) |
| `CategoryTheory.Abelian.SpectralObject.E₂HomologicalSpectralSequenceNat` | [Mathlib/Algebra/Homology/SpectralObject/SpectralSequence.lean:696](https://github.com/leanprover-community/mathlib4/blob/139105d28c7685a154cb3093f79edb2e16708099/Mathlib/Algebra/Homology/SpectralObject/SpectralSequence.lean#L696) |

**New or unverified bridge.** No ready-to-apply finite Koszul double-complex spectral comparison/rank inequality or convergence package matching O_TOR/E_TRANSFER was verified. Presence of abstract spectral sequences does not prove a project degeneration claim.

**Planning consequence.** Do not estimate generic spectral-sequence theory from zero. Consider finite-chain or filtration rank arguments to avoid the substantial application/abutment bridge; an equivalence to the paper use still needs proof.

## EULER: Euler characteristic and finite Betti ranks

**Status:** `definitions_verified_euler_poincare_identity_unverified`.

**Verified reuse.** Euler characteristics of complex terms and homology are defined and converted to finite sums under support hypotheses; all 175 lines of this file were inspected.

| Declaration or source item | Pinned evidence |
|---|---|
| `Module.finrank` | [Mathlib/LinearAlgebra/Dimension/Finrank.lean:61](https://github.com/leanprover-community/mathlib4/blob/139105d28c7685a154cb3093f79edb2e16708099/Mathlib/LinearAlgebra/Dimension/Finrank.lean#L61) |
| `HomologicalComplex.eulerChar` | [Mathlib/Algebra/Homology/EulerCharacteristic.lean:148](https://github.com/leanprover-community/mathlib4/blob/139105d28c7685a154cb3093f79edb2e16708099/Mathlib/Algebra/Homology/EulerCharacteristic.lean#L148) |
| `HomologicalComplex.homologyEulerChar` | [Mathlib/Algebra/Homology/EulerCharacteristic.lean:154](https://github.com/leanprover-community/mathlib4/blob/139105d28c7685a154cb3093f79edb2e16708099/Mathlib/Algebra/Homology/EulerCharacteristic.lean#L154) |
| `HomologicalComplex.eulerChar_eq_sum_finSet_of_finrankSupport_subset` | [Mathlib/Algebra/Homology/EulerCharacteristic.lean:160](https://github.com/leanprover-community/mathlib4/blob/139105d28c7685a154cb3093f79edb2e16708099/Mathlib/Algebra/Homology/EulerCharacteristic.lean#L160) |

**New or unverified bridge.** This file does not itself assert equality of the two Euler characteristics. An exact Euler-Poincare equality elsewhere was not verified by this bounded audit. Betti definition, finiteness and comparison to minimal free ranks remain project obligations.

**Planning consequence.** Finite-dimensional rank-nullity gives a plausible short proof of the needed bounded Euler identity, but it should be scheduled as a lemma to prove, not checked off as imported.

## GROEBNER: Multivariate division and Gröbner tools

**Status:** `division_verified_full_groebner_basis_api_not_found`.

**Verified reuse.** Monomial orders, leading terms, reduction, and division by a family with invertible leading coefficients exist; remainder monomials avoid divisibility by the leading monomials.

| Declaration or source item | Pinned evidence |
|---|---|
| `MonomialOrder.reduce` | [Mathlib/RingTheory/MvPolynomial/Groebner.lean:83](https://github.com/leanprover-community/mathlib4/blob/139105d28c7685a154cb3093f79edb2e16708099/Mathlib/RingTheory/MvPolynomial/Groebner.lean#L83) |
| `MonomialOrder.div` | [Mathlib/RingTheory/MvPolynomial/Groebner.lean:123](https://github.com/leanprover-community/mathlib4/blob/139105d28c7685a154cb3093f79edb2e16708099/Mathlib/RingTheory/MvPolynomial/Groebner.lean#L123) |
| `MonomialOrder.div_set` | [Mathlib/RingTheory/MvPolynomial/Groebner.lean:226](https://github.com/leanprover-community/mathlib4/blob/139105d28c7685a154cb3093f79edb2e16708099/Mathlib/RingTheory/MvPolynomial/Groebner.lean#L226) |

**New or unverified bridge.** Despite its filename, the audited file provides division, not a verified Buchberger algorithm or full Gröbner-basis/initial-ideal/standard-monomial quotient API. Homogeneous division and the specific semigroup initial ideal identifications need proofs/adapters.

**Planning consequence.** Ordinary division machinery is reusable. Do not treat all X_BASIC Gröbner obligations or BHP/EK as solved by importing this file.

## ADD: Finite-additive combinatorics: Kneser and Savchev-Chen

**Status:** `nearby_foundations_verified_exact_named_inputs_not_found`.

**Verified reuse.** General-group min-order Cauchy-Davenport, prime-modulus Cauchy-Davenport, pointwise finite-set operations and stabilizer/small-doubling foundations are available. to_additive also generates an additive min-order version used in the ZMod proof.

| Declaration or source item | Pinned evidence |
|---|---|
| `Finset.cauchy_davenport_minOrder_mul` | [Mathlib/Combinatorics/Additive/CauchyDavenport.lean:116](https://github.com/leanprover-community/mathlib4/blob/139105d28c7685a154cb3093f79edb2e16708099/Mathlib/Combinatorics/Additive/CauchyDavenport.lean#L116) |
| `ZMod.cauchy_davenport` | [Mathlib/Combinatorics/Additive/CauchyDavenport.lean:198](https://github.com/leanprover-community/mathlib4/blob/139105d28c7685a154cb3093f79edb2e16708099/Mathlib/Combinatorics/Additive/CauchyDavenport.lean#L198) |
| `Finset.doubling_lt_three_halves` | [Mathlib/Combinatorics/Additive/VerySmallDoubling.lean:324](https://github.com/leanprover-community/mathlib4/blob/139105d28c7685a154cb3093f79edb2e16708099/Mathlib/Combinatorics/Additive/VerySmallDoubling.lean#L324) |

**New or unverified bridge.** The exact stabilizer-sensitive Kneser theorem for composite cyclic groups and Savchev-Chen long zero-sum-free sequence classification were not found in the recorded source scans. Prime-modulus Cauchy-Davenport is insufficient for composite m; the general min-order bound also does not supply the full Kneser stabilizer correction.

**Planning consequence.** Budget exact Kneser and SC separately as new theorem work unless a later targeted semantic audit identifies substitutes. Existing finsets, ZMod and pointwise sumsets reduce setup cost.

## PUBLISHED: Green, BHP/EK, arithmetic-progression Betti/cone, LTV

**Status:** `exact_published_inputs_not_found`.

**Verified reuse.** General polynomial, module, dimension, grading and finite-set foundations above can support future proofs.

**New or unverified bridge.** Targeted global scans did not find Green hyperplane restriction in the needed form; Bigatti-Hulett-Pardue Betti comparison; Eliahou-Kervaire formula; Gimenez-Sengupta-Srinivasan arithmetic-progression Betti formula; Herzog-Stamate cone equality; or Lan-Tu-Vu three-generator comparison. This is a qualified search result, not a formal absence proof or exhaustive semantic audit.

**Planning consequence.** For axiom-free completion these are separate substantial library projects or must be replaced by fully proved sufficient special cases. Explicit theorem hypotheses are valid for a conditional milestone, but such a milestone must not be called unconditional P14 formalization.

## Rees Noetherian chain and the associated-graded boundary

At this commit the actual source proves:

1. `reesAlgebra I` consists of polynomials whose coefficient in degree `n` lies in `I^n` (`ReesAlgebra.lean:39,64`).
2. `adjoin_monomial_eq_reesAlgebra` identifies the degree-one generating submodule; `reesAlgebra.fg` deduces finite generation from `I.FG` (`:101,115`).
3. The anonymous finite-type instance uses finite generation of ideals over Noetherian `R`; the anonymous Noetherian instance then invokes `Algebra.FiniteType.isNoetherianRing R _` (`:127,130`).
4. With only `IsNoetherianRing (R ⧸ I)` and `I.FG`, `tensorProduct_reesAlgebra_isNoetherian_of_fg` proves the base-changed Rees algebra Noetherian (`:134`).
5. `isNoetherianRing_reesAlgebra_quotient` transports this through `Algebra.TensorProduct.quotIdealMapEquivQuotTensor` to the quotient by `I.map (algebraMap R (reesAlgebra I))` (`:140`).
6. `mem_map_algebraMap_reesAlgebra_iff` says membership in this extended ideal is equivalent to every coefficient `n` belonging to `I^(n+1)` (`:146`).

The final two statements are particularly relevant: the quotient is mathematically the expected Rees model for the associated graded ring, but this audit did not verify an existing direct-sum grading or the required equivalence to successive ideal-power quotients. Choosing that quotient as a project definition does not, by itself, prove the paper’s actual tangent-cone statement.

## Search receipt

All searches use `rg -n -i --glob "*.lean" PATTERN Mathlib` against the pinned checkout. Counts are matching source lines, including comments and geometry false positives. The JSON contains the exact patterns and complete hits.

| Search | Matching lines | Interpretation |
|---|---:|---|
| `numerical_semigroup_apery` | 0 | Targeted lexical evidence only |
| `associated_graded` | 1 | Targeted lexical evidence only |
| `koszul` | 8 | Targeted lexical evidence only |
| `betti` | 0 | Targeted lexical evidence only |
| `minimal_graded_resolution` | 0 | Targeted lexical evidence only |
| `hilbert_syzygy` | 0 | Targeted lexical evidence only |
| `groebner_basis` | 0 | Targeted lexical evidence only |
| `kneser` | 1 | Targeted lexical evidence only |
| `savchev_chen` | 0 | Targeted lexical evidence only |
| `green_hyperplane` | 0 | Targeted lexical evidence only |
| `bhp_ek` | 0 | Targeted lexical evidence only |
| `ap_betti_cone_ltv` | 0 | Targeted lexical evidence only |

For `associated_graded`, a hit for “associated graded object” of a bicomplex forgets differentials and is not an ideal-filtration associated-graded ring. For `kneser`, the hit is a small-doubling file’s reference/TODO; it is not the needed theorem. For `koszul`, differential-geometric Koszul formulas are unrelated to the algebraic complex. For generic resolutions, existing projective/finite-resolution declarations must be distinguished from minimal finite free graded resolutions.

## Scheduling guidance from evidence, not proof counts

No reliable person-month estimate can be extracted from declaration counts. For project estimates, reuse reduces foundational setup for submonoids, linear algebra, quotients, grading, Rees constructions, chains and generic homology. It does not reduce the novel proof into a few imported theorems. The largest uncertainty remains (a) actual-semigroup/tangent-cone and Apéry coordinate equivalences; (b) concrete finite Koszul operations and comparison with intrinsic Betti numbers; (c) precise published inputs, particularly Green/BHP/EK and AP/LTV; and (d) the paper-specific filtered/endpoint rank inequalities.

A useful first implementation checkpoint would elaborate a minimal example of each bridge at this exact commit: numerical-semigroup data to a tangent-cone presentation, finite Koszul differential and d²=0, finite homology finrank, and one short-exact-sequence rank inequality. This is a future checkpoint, not work performed in this PLANONLY audit. Conditional milestones may expose published inputs as theorem hypotheses; unconditional completion must discharge them, without `axiom`, `sorry`, or replacing the intended ring/Betti definition by an unproved surrogate.
