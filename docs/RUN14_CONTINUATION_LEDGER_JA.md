# SDD ledger — plan: docs/superpowers/plans/2026-11-10-run14-green-cut-tower-order.md

Resume baseline: `8040c90138bf1aa76cc99d9a5e7df7b2c1a8a206`; Run13 complete baseline d8556dc.
Existing work checkout explicitly authorized; ordinary Push permission persists. Baseline lake build passed.
Previous `verification/run14/` and PARTIAL archive are frozen. New evidence goes to `verification/run14_continuation/`.

Pre-flight: offset level/path API → actual H budget: sharp volume was absent, fixed by counting first-crossing nonatom residues, then all prefix ranks. Existing H definition is preserved.
Pre-flight: Green → one cut → P-generators → H1≤rδ: numerical rank decomposition alone cannot supply cut; no completed theorem may take Green/cut as an unproved input.
Pre-flight: actual stage quotient → truncated exact sequence: low-degree equality proved previously; high-degree modules and exactness must be constructed over actual action.

Ruling: Preserve authorized existing work checkout and all fixed dependencies — avoid copying the complete Lean build cache — verify current HEAD and baseline content hashes.
Ruling: Prove volume through first-crossing levels and lower ranks of least offsets — this avoids an arbitrary sorted residue enumeration and proves the same (3.1) — if incorrect, the cardinality bound must fail; Lean checks actual highSet witnesses and injections.

Progress:
- [x] `OffsetLevel`: actual atom step, strict at atom residue, each first-reached level≥2 has a distinct actual nonatom Apéry witness, Lρ≤δ+1.
- [x] `FiniteRank`: injective natural weights give a finite rank permutation.
- [x] `OffsetVolumeArithmetic`: full min staircase sum.
- [x] `OffsetVolume`: lρ≤rank(bρ), pointwise min bound and exact δV sharp volume; local module builds green. Full acceptance still to run after root build.
- [x] Green: general degree-two maximal multiplication rank / cut existence.
- [x] One fixed cut and P action restriction.
- [x] Actual truncated tower / generating degrees.
- [x] Actual interval/resource bounds and Data/all_rows.
- [x] Full verification, final fresh review, ledger/paper alignment, audit archive prepared for the authorized release commit/Push.

Continuation milestone:
- Green generic independence is proved by a determinant polynomial over an arbitrary infinite field (`Perturbation`).
- `MaximalRank.maximal_rank_kernel` proves the pencil tangent property by an actual nonzero minor, not a rank assumption on homology.
- `RankChoice` obtains a nonisotropic maximum-rank point when squares are nonzero, by avoiding one quadratic polynomial; no 2 inverse.
- `BilinearSpan` handles symmetric and alternating products separately by Sym2 cardinalities.
- `QuadraticRank` proves dim W≤choose(R+1,2), including characteristic two.
- `HyperplaneStep`, `CutImage`, `FlagSpan`, `HyperplaneFlag` give one independent full flag and all prefix bounds, with actual third-isomorphism maps.
- `QuadraticProduct` is the actual A1×A1→A2 product; live factorizations prove product spanning. All degree parameters are explicit (n=p=1) to avoid failed inference under opaque headDegree aliases.
- `ActualGreen.actual_green_flag` proves actual A degree-two Green bounds, over any infinite k.
- `SquareZeroCut` proves `linearCutData_nonempty`: independent r=max(2,p) forms with the stronger quadratic-span equality, padded in A1 if p<2. `LinearCutData.high_mem` kills all actual degrees≥2 by live degree-two prefixes. `fixedLinearCut` chooses this once.
- Root `lake build` passed including all of these, before adding `LinearForms`. Tests `Run14Volume.lean` and `GreenLinearAlgebra.lean` passed (their two /tmp/*.log files empty).
- `LinearForms.lean` currently being debugged: A1≃non-x coefficients composition is proved, polynomial lift and its coordinate inverse are under local build. Do not claim this connection complete until /tmp/linear_forms.log is green.

Next necessary work (no stopping at this milestone):
1. Finish LinearForms / fixed P restriction and same-cut witness (finite fields use existing InfiniteScalarField).
2. TowerStage quotient coordinates and degree basis/card formula. Identify H_t with Apéry / terminal intervals.
3. Prove residue-disjoint intervals ⇒ H_t≤m−1; sum interval lengths plus terminal_residue_sum ⇒ mass=Σ(L−1)≤δV; H1 identity/ℓ bound ⇒ head cap.
4. Strong quadratic span of the chosen C gives surjective maps (Fin r→A_n)→A_{n+1}, by live degree-two prefix; descend to U_s to get H1≤rH0=rδ. This avoids any need to assume an A-image algebraic independence.
5. Build actual P-submodules X_s/M_s and truncated short exact sequence with K_s=existing actual ascendingJump stratum, plus single-degree generation from the same recurrence. Full S0 action already acts on ideal quotients via standard quotient algebra instances.
6. Assemble Data using fixed actualLayers and actualNumericalBoundary; pass all_rows. Run15 Tor/target stays out.
7. New continuation verifier, all regression/frozen files, new declaration audit (compress huge explicit type evidence rather than repeat 50MB plain files), final one fresh whole-branch reviewer, paper ledger, COMPLETE archive only if every goal closed, normal Push.

Further milestone (local builds green):
- `ActualGreen` now compiles: full actual A prefix-degree bound is proved through a surjective map from the bilinear cut quotient onto the actual ideal quotient piece.
- `SquareZeroCut` compiles, strengthened to a `quadratic_span` field rather than merely ideal membership. This supports genuine single-degree generation without a hidden homogeneity assumption on arbitrary ideal coefficients.
- `LinearForms` and `TowerCoordinates` compiled successfully together after switching the linear map to library `Fintype.linearCombination`; do not reintroduce hand-built map_add/smul proofs with opaque NonXAtom aliases. `Pi.single` needs `Function.update_apply` when simplifying sums. No unsafe reducibility attribute is used.
- `TowerCoordinates` provides actual stage quotient coordinates and `towerStageDegree_finrank` as the card of actual surviving head-degree labels.
- `CutAction` and `Green/FormProducts` are under the latest combined build /tmp/cut_action.log. FormProducts had one type-inference hole in product_mem_cutImage; all arguments have now been made explicit.

Resource closure milestone:
- `CutGeneration` compiles: the *same* Green cut gives actual A_n→A_(n+1) finite product surjections, then actual U_s degree surjections, hence H1≤rδ.
- `TerminalResidues`, `IntervalMass`, `HeadResource` compile: actual intervals, field-independent H, residue disjointness, full total mass equality, sharp δV budget, H1+a=δ+ell and ell≤e−1.
- `ActualResources` compiles: the actual Data constructor over any k (finite fields via fixed infinite cut and proved H field independence), and `actual_all_rows` using actual Sidon boundary. This is numerical closure only, as prescribed; Run15 remains actual Tor/target.
- `HighIdeal` and `TowerExact` compile: actual degree truncation ideals, Xν+1=0, actual S₀ short exact sequence with K=F_s image. `TowerStratum`/`TruncGeneration`/`TruncCoordinates` are currently under local build /tmp/trunc_generation.log; finish these connections before claiming tower complete.

Implementation closure milestone:
- `TowerStratum` compiles: actual K is Run12's ascending stratum over S₀, then restricted to the fixed P.
- `TruncGeneration`, `CutAugmentation`, `FixedTower` compile: X/M single-degree generation, variable multiples equal the next actual truncation, and actual P short exactness with inherited same-jump degree shift.
- `CutGeneratorCount` compiles: explicit coefficient structure through P, actual augmentation quotient ≃ actual bottom degree, minimal generator count = actual degree finrank.
- `Ordinary/ActualWitness` compiles: one source + one cut on the fixed infinite same-characteristic extension; the Data constructor uses that exact cut. All numeric parameters/H derive from source.
- Root build green, 5182 jobs. Historical goal proofs and acceptance are included in the fresh full suite, now running; do not report final completion before its axiom audit and final review.

Final review: fresh `/root/run14_final_review`, read-only whole-branch pass, all 38 new core sources + interfaces + verifier. Critical 0, Important 0, blocking Minor 0.
Final: Ruling: P→S₀ injectivity not exported — this run uses the formal polynomial P and explicit actual action with independent linear lifts; current conclusions do not treat P literally as a subring — a future subring consumer must prove that identification first.
Final: Ruling: reviewer did not judge final audit/package/push — root owns fresh machine evidence, manifest/hash checks, normal Push and remote confirmation — completion would be unsupported if these were skipped.
Final: Ruling: reviewer did not independently compare original manuscripts/publications beyond supplied plan/alignment — preserve exact scope and record alternative proof A44–A49 for later mathematical audit — formal Run14 closure is not certification of every manuscript claim.
Final: Ruling: reviewer excludes Run15 actual Tor/target/P14 — preserve the explicitly requested Run15 boundary — including those claims now would overstate completion.
Final self-detected verification fix: environment coverage assertion rejected two anonymous examples (tests/GreenLinearAlgebra and Run14Volume), despite kernel compilation. Preserve RED log, promote them to named public acceptance theorems, then rerun the entire suite and environment audit. No production theorem changed.

Final mathematical verification: scripts/verify_run14_continuation.py → PASS_RUN14_CLOSURE, 50/50 commands, 3217 environment declarations, all 544 new declarations, 241 frozen source/dependency/evidence paths. Anonymous-example coverage fix GREEN. All new explicit types compressed, only allowed three axioms. Production branch final review already clear.
Integration: fetched actual origin/work aa6bf4c (Run13 verifier cache/dependency repair), fast-forwarded without conflicts or changes to Lean production. Preserved remote repair files byte-for-byte; final verifier also freezes these and explicitly builds test prerequisites, then reruns full checks. Normal Push remains pending final archive/commit.

Final reproducibility fix: fetched Run13 fixture-cache repair exposed that replaying its historical command list retained the old fixture order. Reproduced a real missing Run13Fixtures.olean failure (FIXTURE_CACHE_RED.log), then topologically ordered predecessor checks from their actual public fixture imports. Added explicit test dependencies and --fresh-test-cache, preserving the old generated cache under /tmp. Final full suite is running from an empty project test cache, so proof checking cannot rely on previously compiled fixture oleans. Production code unchanged.

Final fresh-cache verification: PASS_RUN14_CLOSURE, 50/50 commands, 3217 environment declarations, all 544 new declarations (514 core +30 acceptance/audit), only propext/Classical.choice/Quot.sound. Frozen original paths 241 plus remote repair paths 74; fresh fixture order 32 before18 verified. Sum of measured check times 168.52 seconds. Both verification fixes RED→GREEN under the full suite. Final archive is produced from this verified tree; normal work-branch commit/Push follows.
