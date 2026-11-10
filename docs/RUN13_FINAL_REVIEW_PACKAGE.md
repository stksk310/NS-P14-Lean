# Run13 final whole-worktree review dispatch package

This is the frozen pre-fix review package. The completed one-pass fixes and final source snapshot are recorded in
`docs/RUN13_CONTINUATION_REVIEW_JA.md` and `verification/block13_continuation/SOURCE_SHA256.json`.

Read-only review. Do not mutate checkout/index/HEAD. Do not delegate.

Base Run12: 6b8d16889ea9b4d88567f0d9ac70391db2a49824.
Prior partial/pushed HEAD: 92cbe8f875845fbcefc76c6c819780fe8776429c.
The continuation is UNCOMMITTED; inspect current files, including untracked sources, not only git diff.
Current core root build134 passes all 4938 jobs. Full suite is running: /tmp/run13c-verification4.log;
final machine evidence will be verification/block13_continuation/{verification,declarations}.json.

Spec: docs/superpowers/plans/2026-11-10-run13-koszul-tor-foundations-order.md and its roadmap.
Coverage draft: docs/RUN13_REMAINING_DECLARATIONS_JA.md.
Rulings: docs/RUN13_EXECUTION_LEDGER_JA.md (Ruling: lines) and paper A34–A39.
Status JSON is deliberately pending review and full verification. LEAN_PROGRESS old partial section is
historical and will get a continuation completion section after review, not silently overwritten.

Question: does this work satisfy ALL specified Run13 foundations? Identify any Important gap precisely.
Do not equate a successful Lean build with satisfying the mathematical spec. In particular examine:
- minimal tower has actual exact covers/bases/minimal action condition and constructs genuine resolution;
  rank equality is proved via syzygy LES, not general Tor/Tor' balancing.
- actual G/T/A/N/Q/strata grading witnesses tie to preexisting degrees;
  actual same-jump Koszul iso shifts t to t+s.
- GradedBaseChange uses the standard extension grading: degree-t complex L⊗k K_t;
  it explicitly includes these complexes into the changed-polynomial Koszul complex and decomposes H.
  Actual G/T/A/N/Q coefficient changes are separate, polynomial-linear coordinate-matrix isos.
  Assess whether any further required identification with the separately constructed L-degree witness
  is missing; do not silently bless a different grading.
- homology finiteness and ordinary Tor are actual proved comparisons, never assumed input.
- generic exact finite vector complex rank Euler will be instantiated in later runs; future actual cut,
  initial ideal, tower/connecting ranks and public inputs are explicitly outside this Run13.
- environment audit must enumerate generated declarations and structure projections, not only regex defs.

## Review Focus (verbatim)

1. Run12の`S.PolynomialRing k`は非x原子のe−1変数S₀。Gのintrinsic Bettiを測る全e変数の最小表示環、および将来のr変数cut環Pと混同しない。
2. Gなどのchain groupはk上無限次元になり得る。homologyの有限性を証明してからfinrankを使い、無限次元でのfinrank=0を消滅証明に使わない。
3. Koszulの符号・augmentation・次数・d²=0は任意標数で成立させる。標数2を別のrank一致の仮定で処理しない。
4. 体拡大は実際のgraded piece・加群・複体の自然写像で扱う。無限形式級数環そのもののテンソル積が常に形式級数環と同型、とは仮定しない。
5. connecting mapと非負補正項の添字を保持する。商のBetti単調性、spectral sequenceの退化、globalなT≅Nは使わない。


## Current core source inventory

- NSP14/Homological/ActualCoefficientBaseChange.lean
- NSP14/Homological/ActualGradedTransport.lean
- NSP14/Homological/ActualGrading.lean
- NSP14/Homological/ActualKoszulTransport.lean
- NSP14/Homological/ActualTorTransport.lean
- NSP14/Homological/Betti.lean
- NSP14/Homological/CofiberNaturality.lean
- NSP14/Homological/CompletedGradedTransport.lean
- NSP14/Homological/ConeExactness.lean
- NSP14/Homological/CoordinateBaseChange.lean
- NSP14/Homological/CoordinateGrading.lean
- NSP14/Homological/DirectSumHomology.lean
- NSP14/Homological/FieldExtension.lean
- NSP14/Homological/FilteredComparison.lean
- NSP14/Homological/FreeKoszulHomology.lean
- NSP14/Homological/GradedBaseChange.lean
- NSP14/Homological/GradedBetti.lean
- NSP14/Homological/GradedKoszulComplex.lean
- NSP14/Homological/GradedKoszulHomology.lean
- NSP14/Homological/GradedModule.lean
- NSP14/Homological/HomologyBaseChangeNaturality.lean
- NSP14/Homological/HomologyRanks.lean
- NSP14/Homological/KoszulAnnihilation.lean
- NSP14/Homological/KoszulAugmentation.lean
- NSP14/Homological/KoszulChainDimension.lean
- NSP14/Homological/KoszulCoefficientBaseChange.lean
- NSP14/Homological/KoszulComplex.lean
- NSP14/Homological/KoszulContraction.lean
- NSP14/Homological/KoszulExactness.lean
- NSP14/Homological/KoszulFinite.lean
- NSP14/Homological/KoszulFree.lean
- NSP14/Homological/KoszulGradedMaps.lean
- NSP14/Homological/KoszulGrading.lean
- NSP14/Homological/KoszulH0Naturality.lean
- NSP14/Homological/KoszulLongExact.lean
- NSP14/Homological/KoszulLowDegree.lean
- NSP14/Homological/KoszulNaturality.lean
- NSP14/Homological/KoszulPolynomialBaseChange.lean
- NSP14/Homological/KoszulPolynomialResolution.lean
- NSP14/Homological/KoszulRanks.lean
- NSP14/Homological/KoszulResolution.lean
- NSP14/Homological/KoszulTor.lean
- NSP14/Homological/KoszulTorNaturality.lean
- NSP14/Homological/KoszulZeroAction.lean
- NSP14/Homological/MinimalFreeTower.lean
- NSP14/Homological/MinorRank.lean
- NSP14/Homological/ModuleProducts.lean
- NSP14/Homological/PolynomialBaseChangeFinite.lean
- NSP14/Homological/PolynomialBaseChangeFunctor.lean
- NSP14/Homological/PolynomialBaseChangeModule.lean
- NSP14/Homological/PolynomialBaseChangeNaturality.lean
- NSP14/Homological/PolynomialLinearMaps.lean
- NSP14/Homological/PolynomialModules.lean
- NSP14/Homological/Presentation.lean
- NSP14/Homological/PresentationGrading.lean
- NSP14/Homological/PrincipalBetti.lean
- NSP14/Homological/RankEuler.lean
- NSP14/Homological/ResidueBetti.lean
- NSP14/Homological/ScalarConeMaps.lean
- NSP14/Homological/StandardMonomials.lean
