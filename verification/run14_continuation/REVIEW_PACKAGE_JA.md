# Run14 continuation final branch review
Base/HEAD on entry: 8040c90138bf1aa76cc99d9a5e7df7b2c1a8a206; changes currently UNCOMMITTED, including untracked source files. Review working tree, not only git diff. No implementing agents were used.
Plan: docs/superpowers/plans/2026-11-10-run14-green-cut-tower-order.md
Ledger and rulings: docs/RUN14_CONTINUATION_LEDGER_JA.md
Exports/current boundary: docs/RUN14_REMAINING_DECLARATIONS_JA.md
Manuscript correspondence: docs/LEAN_PAPER_ALIGNMENT_JA.md A44–A49.
38 new core files, 3112 lines before last generator-count/witness additions were counted; exact source list below is authoritative.

Architecture: arbitrary-characteristic Green via maximal-rank pencil/minors, actual bilinear product, one fixed cut over k(X), actual S0/P restrictions and truncated tower, augmentation quotient generator count, interval resource identities/caps, sharp offset volume, actual NumericalClosure.Data/all_rows with actual Sidon Boundary. Run15 actual Tor-to-row and target Betti remain deliberately outside scope.

Verification: fresh root build passed 5182 jobs. Full predecessor suite passed 43 commands before a new acceptance proof spelling failed; that spelling has been corrected and the full suite is being rerun. Script and logs /tmp/verify_run14_continuation.log; final evidence verification/run14_continuation/verification.json. All old production/tests/dependencies/verification/run14 and old PARTIAL ZIP are frozen by the verifier. New declarations, generated helpers and instances all audited by collectAxioms with only propext/Classical.choice/Quot.sound; explicit new types in compressed evidence. Historical RemainingGoals unchanged, all five old propositions are now proved in audit/run14_continuation/ClosedGoals.lean.

Important review targets: no conclusion weakened to match available formalization; no arbitrary H or Green/cut/resource hypotheses replacing actual construction; no cut mixing; finite fields/characteristic two; natural subtraction and zero residue; degree truncation/kernel and actual P linearity; minimal generator quotient; full tail support; r=2 guard. Polynomial forms are proved linearly independent in S0; A image need not be independent.

Read-only, do not mutate files/index/branch or run concurrent lake builds. No further subagents. Give specific Critical/Important/Minor findings with file:line, verdict, and an explicit Declined to judge list. This is the single fresh whole-branch reviewer; final implementation/verification ownership stays with root.

## New core sources
- NSP14/Combinatorics/FiniteRank.lean
- NSP14/Green/BilinearQuotient.lean
- NSP14/Green/BilinearSpan.lean
- NSP14/Green/CutImage.lean
- NSP14/Green/ExtendIndependent.lean
- NSP14/Green/FlagSpan.lean
- NSP14/Green/FormProducts.lean
- NSP14/Green/HyperplaneFlag.lean
- NSP14/Green/HyperplaneStep.lean
- NSP14/Green/MaximalRank.lean
- NSP14/Green/Perturbation.lean
- NSP14/Green/QuadraticRank.lean
- NSP14/Green/RankChoice.lean
- NSP14/Ordinary/ActualWitness.lean
- NSP14/Ordinary/OffsetVolumeArithmetic.lean
- NSP14/Semigroup/ActualGreen.lean
- NSP14/Semigroup/ActualResources.lean
- NSP14/Semigroup/CutAction.lean
- NSP14/Semigroup/CutAugmentation.lean
- NSP14/Semigroup/CutGeneration.lean
- NSP14/Semigroup/CutGeneratorCount.lean
- NSP14/Semigroup/FixedTower.lean
- NSP14/Semigroup/HeadResource.lean
- NSP14/Semigroup/HighIdeal.lean
- NSP14/Semigroup/IntervalCap.lean
- NSP14/Semigroup/IntervalMass.lean
- NSP14/Semigroup/LinearForms.lean
- NSP14/Semigroup/OffsetLevel.lean
- NSP14/Semigroup/OffsetVolume.lean
- NSP14/Semigroup/QuadraticProduct.lean
- NSP14/Semigroup/SquareZeroCut.lean
- NSP14/Semigroup/TerminalResidues.lean
- NSP14/Semigroup/TowerCoordinates.lean
- NSP14/Semigroup/TowerExact.lean
- NSP14/Semigroup/TowerIntervals.lean
- NSP14/Semigroup/TowerStratum.lean
- NSP14/Semigroup/TruncCoordinates.lean
- NSP14/Semigroup/TruncGeneration.lean

## Acceptance and audit
- tests/GreenLinearAlgebra.lean
- tests/Run14Volume.lean
- tests/Run14Closure.lean
- audit/run14_continuation/ClosedGoals.lean
- scripts/verify_run14_continuation.py
