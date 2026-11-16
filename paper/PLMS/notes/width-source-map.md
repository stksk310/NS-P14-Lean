# Narrow-width section: source and declaration map

The fragment is `sections/width.tex`, Section `sec:width`, Proposition
`prop:narrow`. The mathematical source is the final form of the narrow-width
argument, including the Run19/20 corrections to the Japanese chapters.
The immutable Lean reference is
[stksk310/NS-P14-Lean at a5e122a4d09536b1609c5faa8d419f8faf81671f](https://github.com/stksk310/NS-P14-Lean/tree/a5e122a4d09536b1609c5faa8d419f8faf81671f).

Local Japanese inputs read:

- `sources/proof_sharp_v6/chapters/01_COMMON_JA.md`;
- `sources/proof_sharp_v6/chapters/04_WIDTH_JA.md`;
- `sources/proof_sharp_v6/chapters/04A_ANTIPODAL_JA.md`;
- `sources/proof_sharp_v6/chapters/05_N4_JA.md`;
- `sources/docs/RUN17_PAPER_CORRESPONDENCE_JA.md`;
- `sources/docs/RUN18_PAPER_CORRESPONDENCE_JA.md`;
- `sources/docs/RUN19_PAPER_CORRESPONDENCE_JA.md`;
- `sources/docs/RUN20_PAPER_CORRESPONDENCE_JA.md`.

The two final closure files were read locally. The more detailed Lean files
listed below were retrieved through the GitHub connector at the pinned commit,
without using the current default branch. No Lean build was run in the paper
workspace. Algebraic identities in the draft were additionally checked with
symbolic rational arithmetic.

## Common notation and scope

`P` in the fragment is `D.coreP k`, the dimension of the actual core endpoint
quotient `D.QCoreModule k`. It is not the dimension of an endpoint quotient of
the actual tangent cone. `R` is `D.actualR k`, and the bound `Rhat` is `D.Rhat`.
`W` is `D.wordVolume`. The orientation of `D` is fixed throughout.

The physical width is `D.d * D.u`. The normalized width is `D.u`. The
proposition's target remains the literal interval completion of the original
source, with its own actual minimal presentation and polynomial ring. The
arithmetic progression equality case `d=1` is handled by equality of carriers;
there is no claim that a normalized width is itself the physical width.

The section's endpoint resources and row estimates are restatements of
`sections/endpoint.tex` (labels `eq:endpoint-resources`, `eq:endpoint-bound`,
`eq:endpoint-rows`, `eq:endpoint-two-rows`). The mathematical role of the kernel
length compensation is retained in `eq:width-transfer` and
`eq:width-rows`; no quotient-Betti monotonicity is invoked.

## Statement--declaration correspondence

The following namespaces are used below: `Data` abbreviates
`NSP14.Endpoint.Data`, `NS` abbreviates `NSP14.NumericalSemigroup`, and `N4`
abbreviates `NSP14.NarrowFour`.

| Paper statement or argument | Final Lean declaration / implementation |
| --- | --- |
| Proposition `prop:narrow`, embedding dimension at least five | `NS.narrow_width_comparison`, `NSP14/Width/Closure.lean` (read locally). Its case split is `e=5`; otherwise `u=q+1`, `u=q+2`, sparse `2e-2≤u`, or dense `u=q+1+t`, `2≤t≤q`. |
| Proposition `prop:narrow`, embedding dimension four | `N4.narrow_four_comparison`, `NSP14/NarrowFour/Comparison.lean` (read locally). It keeps all fields, all rows, original source and literal target. |
| Transport between equal semigroup carriers in the four-generator closure | `N4.completed_carrier_betti` and `N4.interval_carrier_betti`, `Comparison.lean`. The conductors/cofinite witnesses are not identified as extra structure. |
| Full arithmetic progression, `u=q+1` | `NS.narrow_fullAP_comparison`, `Width/EdgeAP.lean`, as indexed in Run18/20; four-generator application also has the directly read `NS.narrow_four_fullAP_comparison` in `NarrowFour/HigherRows.lean`. The source bound is `i C(u+1,i+1)` for `d>1`; the `d=1` route uses actual carrier equality. |
| One-hole geometry, quadratic basis, original height and resource bounds | `Width.EdgeHoleGeometry`, `Width.EdgeHoleResources` and their consumers in the directly read `Width/EdgeHoleComparison.lean`. Run18 records the actual degree/offset geometry and the height bound `H_x≤1`. |
| One-hole signed-unit rank lower bounds | `Data.OneHole.actual_boundary_rank` and `Data.OneHole.minor_card_pair`, used directly in `Data.OneHole.actual_upper_add`. Supporting modules are `Width.EdgeHoleAction`, `Width.EdgeHoleMinor`, `Width.EdgeHoleWedgeCount` and `Homological.KoszulCombinedMinor`. |
| Combined one-hole inequality `β_i+δ C(q+1,i)≤i C(q+2,i+1)+T_i`, assuming `P+δ≤q+3` | **Exactly** `Data.OneHole.actual_upper_add`, `Width/EdgeHoleComparison.lean`. The draft uses `δ=0` for an interior hole, `δ=1` for an end hole. |
| The two bounds on `T_i` | `NSP14.Width.edgeCorrection_le_choose` and `NSP14.Width.edgeCorrection_le_choose_pred`, directly read in `Width/EdgeHoleCounting.lean`. The auxiliary `edge_summand_le` is the fixed-subset inequality written in the prose. The second bound requires `r+s≥3`. |
| End-hole top indicators | `edgeCorrection_zero_left`, `edgeCorrection_comm`, `edgeTopCorrection_le`, same file. Both `i=q` and `i=q+1` are retained. |
| One-hole comparison | `Data.OneHole.actual_positive` and `NS.narrow_oneHole_comparison`, `Width/EdgeHoleComparison.lean`. Its hypothesis is `e≥5`; the draft explicitly restricts this paragraph to `q≥3`, leaving `q=2` to the later four-generator treatment. |
| Dense distance and original height resources, `eq:width-dense-resources` | `Width.DenseVolume`, `Width.DenseHeight`, `Width.DenseResources`, as recorded by Run18. These supply `W=q+1+2t`, `P≤W`, `R≤t`, and `R=0` for `t≤2`. |
| One lex quotient having the full Hilbert function of the same core | `Data.exists_core_lex`, used directly in `Data.dense_core_lex_bound_two_branch`, `Width/DenseLexResources.lean`. Its supporting modules are `Width.CoreLexPresentation`, `Lex.LexExistence`, `Lex.TotalBettiComparison`. |
| Lex generator telescoping and `K` in `eq:width-lex` | `Lex.StandardBettiWeights`, `Lex.PrefixGeneratorCorrection`, `Lex.StableDegreeDecomposition`, as described in the final Run18 entry; the consumer `dense_core_lex_bound_two_branch` was read directly. |
| Weighted child/parent bound on `K` | `Data.dense_lex_correction_bound`, `Width/DenseLexResources.lean`, using `Lex.IsLex.correction_tail_third_bound`. It has `r≤q`, `r≥2`, and `2t≤C(r+1,2)`. |
| Dense `K≤2` for `t=2`, `3K≤2t(t-1)` for `t≥3` | `Data.dense_core_lex_bound_two_branch`, same file. This is the two-branch final export. The compatibility declaration `dense_core_lex_bound` also records the `t=3`, `K≤4` specialization. |
| Dense capacity inequality in all rows | `NSP14.Width.dense_payment`, with `dense_payment_two`, `dense_payment_ge_three`, `dense_gamma_nonneg`, in the directly read `Width/DensePayment.lean`. Its consumer is `NS.narrow_dense_comparison` in `Width.DenseComparison`, as indexed in Run18/20. |
| Normalized row capacity increases with row index | `Width.NormalizedCapacity`, indexed in Run18, and the directly read `NSP14.Width.higher_capacity_from_second`, `Width/HigherFromSecond.lean`. |
| Resource envelope and propagation `eq:width-propagation` | `Data.actual_resource_envelope_add` and `Data.actual_higher_from_second`, same file. The same rational `B` bounds `P` and `Rhat+u`. Row `i=e` is included. |
| General Kneser growth and tail sum | `NSP14.Additive.proper_sum_growth`, `generated_sum_growth`; `Data.wordVolume_tail`, `wordVolume_growth_bound`, as indexed in Run17. The source's residue alphabet is `Data.residueAlphabet`, with actual cardinality and generation proved there. |
| Sparse quadratic and remainder envelopes | `Width.SparseVolume`, `Width.Progression`, `Width.SparseRemainder`, as indexed in Run18/20. Their statements concern arbitrary widths in the applicable ranges, including composite modulus. |
| Sparse first-row inequalities and nonnegative differences | `Width.FirstResources`, `Width.SparseFirstSmall`, `Width.SparseFirstLarge`, `Width.SparseFirst`, indexed in Run18/20. The displayed `e=6,7,8,9` formulas are polynomial identities for every `z≥0`, rather than data about bounded widths. |
| Sparse second row and higher rows | `Width.SparseSecond`, `Width.SparseHigher`; the final original-source theorem `NS.narrow_sparse_comparison` was read directly in `Width/SparseComparison.lean`. The `e=6` factor and `e=7+v` polynomial match the final Run18 simplification. |
| Five-generator widths `u=6,7` | `Data.actual_five_small_first`, `actual_five_small_positive`, `NS.narrow_five_small_comparison`, directly read in `Width/FiveSmall.lean`. |
| Conditional improvement at `u=7`, `R>0` only | `Data.coreHilbert_two_add_five_le_P_of_R_pos` and `Data.QCore_five_seven_first`, same file. The draft's degreewise harmonic explanation proves the same sufficient bound `b_1≤9`. At `R=0` the weaker `b_1≤10` is retained. |
| Five-generator higher rows, all structures | `Data.actual_five_higher`, directly read in `Width/FiveHigher.lean`. It uses the same propagation lemma as the sparse branch, `B=14` at `u=8`, `B=u²/4` for `u≥9`, and the displayed cubic `2z³+33z²+136z+33`. |
| Exact tail retained at `u=8` | `NSP14.Width.five_wordVolume_eight`, same file. Only `W≤14` is used. |
| Four-point alternative and actual antipodal offsets | `NSP14.Additive.fourPoint_small_growth`, `twoCoset_antipodal`, `fourPoint_growth`, indexed in Run17; `Data.antipodal_offsets`, read directly in `Width/AntipodalComparison.lean`. The conclusion is about the original integer offsets, without a unit action on the semigroup. |
| Non-antipodal first row and integer slack | `Width.FiveNonAntipodal`, its consumer `NS.narrow_five_large_comparison` in the directly read `Width/AntipodalComparison.lean`; `NSP14.Width.nonAntipodal_integer_payment`, directly read in `Width/IntegerPayment.lean`. |
| Candidate-word spanning bound `P≤C(h+1,2)+1` | `Data.antipodal_minimal_normal_form`, `antipodalBasisMap_surjective`, `antipodalCandidate_card`, `antipodal_coreP_bound`, directly read in `Width/AntipodalCore.lean`. This route only needs `0<t<h` and the stated configuration, not a proof that these candidates are independent. |
| Antipodal first row | `Data.actual_antipodal_first`, `Width/AntipodalComparison.lean`, using `NSP14.Width.antipodal_integer_payment`, `Width/IntegerPayment.lean`. The displayed slack is uniform for `h≥4`. |
| Five-generator closure | `NS.narrow_five_comparison`, `Width.FiveComparison`, indexed in the final correspondence and used by the locally read `Width/Closure.lean`. |
| Two-variable standard words and actual core cardinality | `NarrowFour.CoreWords`, indexed in Run19/20; consumer declarations in the directly read `SocleTriangle`, `Distance`, `FirstCount`, `SmallWidths` files all concern this same downset. |
| Socle corners and actual triangle inclusion | `N4.socleWordEquiv`, `sigma_card`, `socle_triangle`, `socle_triangle_card`, `standard_of_degree_lt_sigma`, directly read in `NarrowFour/SocleTriangle.lean`. The triangle is an inclusion in the actual standard-word downset, not just a cardinality inequality. |
| Two-variable distance and `σ≤u-1` | `N4.distance_volume_floor`, `distance_volume_four_add`, `sigma_le_width`, directly read in `NarrowFour/Distance.lean`. |
| Pure and mixed standard-word lengths, `eq:width-word-length` | `N4.standard_mixed_bound`, `standard_pure_bound`, `standard_length_bound`, directly read in `NarrowFour/StandardWords.lean`. Both pure and mixed arguments use the sequence theorem in the final Lean. |
| Return from unit-normalized sequence to original offsets | `N4.power_relation_forbidden`, `standard_power_relation_bound`, `twoValue_budget`, same file; upstream `Additive.savchevChen`, `savchevChen_positive`, `savchevChen_twoValue` are indexed in Run17. No cone or height is transported by the unit. |
| Original height and `R=0` for `u≤5` | `N4.coreHeight_two_bound`, `actualR_zero_small`, same file. This is stronger than the old chapter's explicit `u≤4` observation. |
| Envelopes `U_2,U_3,U_4` | `N4.actual_higher_envelopes`, directly read in `NarrowFour/HigherRows.lean`. The `U2`, `U3`, `U4` definitions are in `NarrowFour/CubicPayment.lean`. |
| Cubic `eq:width-four-cubic` | `N4.cubic_gap` and `second_payment`, directly read in `NarrowFour/CubicPayment.lean`. Coefficients are exactly `(36,140,45,4)` in ascending degree. |
| Higher-row comparison by envelope differences and target ratios | `N4.envelope_three`, `envelope_four`, `ratio_three`, `ratio_four`, `second_le_third`, `second_le_five_fourth`, `third_payment`, `fourth_payment`, same file. No separate quartic or quintic payment is used. |
| Small higher rows `u=5`: `(18,7,0)`; `u=4`: `(12,5,0)` | `N4.actual_small_higher`, `actual_width_four_higher`, directly read in `NarrowFour/HigherRows.lean`. The draft uses the final `R=0` through width five. |
| All physical targets for four-generator higher rows | `N4.physical_capacity` and `narrow_four_higher`, same file. |
| Three forbidden relations and guarded triangle removal | `NarrowFour.Relations` and `N4.coreP_count_add`, `first_count`, directly read in `NarrowFour/FirstCount.lean`. The guard `κ≤h` is retained, so no negative binomial index is turned into a natural-number subtraction. |
| Large first row and width five | `NarrowFour.FirstLarge`, indexed in Run19/20; `SmallWidths.lean` directly uses `N4.actual_first_five`. |
| First rows `u=6,7,8` | `N4.height_six_nonexception`, `actual_first_six`, `actual_first_7`, `actual_first_8`, directly read in `NarrowFour/SmallWidths.lean`, with the explicit `strip_6_1_5`, `strip_7_*`, `strip_8_*` declarations. |
| Width-four joint box bound and ordinary pairs | `N4.box_two_joint`, `ordinary_four_first`, `actual_first_four_coarse`, same file. The bound `P+σ≤5` is proved for the same downset, not by combining incompatible extremal estimates. |
| All small first-row consumers except the special width-four family | `N4.narrow_four_small`, same file. |
| Core normal columns for `(a,b,u)=(1,3,4)` | `NarrowFour.WidthFourCore`, indexed in Run19/20, and the directly read normalization in `NarrowFour/WidthFourInitial.lean`. |
| Exact all-`j` competition and integer thresholds | `N4.WidthFour.free_coordinates`, `free_exists_iff`, `delta_identity`, `delta_neg`, `kappa_monotone`, `all_j_threshold`, directly read in `NarrowFour/WidthFourCompetitors.lean`. |
| Restricted columns cannot be longer competitors | `N4.WidthFour.restricted_long_impossible`, same file. This is the final Lean route; the old chapter's alternative description of redundant restricted competition is unnecessary. |
| Surviving columns and independence in actual tangent algebra | `N4.WidthFour.column_dead_iff`, `column_zero_iff`, `live_degree`, `live_images_independent`, same file. Independence uses actual coefficient duals, with no finite-dimensionality assumption on all of `G`. |
| Actual defining ideal is four core binomials plus five tails | `N4.WidthFour.actual_kernel_eq`, `actualPresentation`, directly read in `NarrowFour/WidthFourInitial.lean`. This is equality of the actual kernel with the candidate ideal. |
| Bound first Betti by a selected generating family | `N4.WidthFour.first_generator_number`, `first_le_generators`, same file; consumer `actual_first_le_family`, `first_le_selected` in the directly read `WidthFourComparison.lean`. |
| Threshold values and generating-family sizes `6,8,8,6`, plus `m=6` | `N4.WidthFour.theta_four_zero`, `theta_four_one`, `theta_four_two`, `theta_four_three`, `candidate_reduced_zero`, `candidate_reduced_one`, `candidate_reduced_two`, `candidate_reduced_three`, `candidate_reduced_six`, `actual_first_bound`, `generatorBound_payment`, directly read in `NarrowFour/WidthFourComparison.lean`. These are sufficient generating-family upper bounds, not assertions of minimality. |
| Final special family comparison | `N4.WidthFour.width_four_comparison`, same file. Higher rows come from `narrow_four_higher`; only row one needs the family calculation. |

## Deliberate changes from older chapter wording

1. **One-hole ranks:** the draft states the combined sufficient bound exported
   by `OneHole.actual_upper_add`; it does not state an exact Koszul rank or an
   exact core Betti formula. The proof uses the actual signed-unit minors.
2. **Antipodal data:** only the candidate-word spanning bound on `P`, generic
   `W≤h²`, and `R≤W-u` appear in the main argument. The exact antipodal
   presentation, exact `P` or `W`, and an exact first-Betti formula are absent.
3. **Four-generator height:** final `R=0` for `u≤5` gives the higher-row bound
   `(18,7,0)` at `u=5`. The older chapter's `(24,13,2)` is not repeated.
4. **Four-generator payment:** the final cubic is
   `4z^3+45z^2+140z+36`. The third and fourth rows use envelope differences
   and binomial-ratio identities. There are no old quartic/quintic payments.
5. **Width four:** the argument identifies the actual defining kernel by
   reduction and actual-column independence. It does not assert a general
   initial-ideal Betti theorem or an unneeded equality `in(I_G)=J`.
6. **Generating-family sizes:** the paper says “at most,” consistent with the
   selected-family Lean proof; it does not claim those displayed generators
   are minimal.
7. **Finite tables:** the small-width tables organize explicit forbidden-word
   and strip inequalities. The proof makes no use of the historical 196 core
   certificates, 665 comparisons, 83 profiles, or a bounded cutoff on `m,d`.
8. **Five-generator condition:** the `b_1≤9` improvement at width seven is
   invoked only when the original actual `R` is positive.

## Remaining editorial considerations

- The section is approximately 2,500 whitespace-delimited words with many
  displayed formulas. No TeX compile was run by this drafting agent; the root
  agent is compiling the integrated document.
- The BHP citation should include the positive-characteristic lex comparison
  used in the final statement (Pardue's extension), not imply a characteristic
  zero restriction. The bibliography metadata is handled separately.
- The additive argument is stated using Kneser's theorem and Savchev--Chen's
  theorem, while the Lean implementation of the latter follows the equivalent
  connected-rearrangement route described in Run17. The paper does not need
  implementation details to cite the mathematical theorem.
- The one-hole result is scoped to `q≥3`; four-generator normalized widths
  three and four are handled explicitly later. This is necessary for the
  second correction estimate's `r+s≥3` hypothesis.
- The section's same-core and same-orientation statements should survive
  stylistic editing: reflection or a unit change of the numerical semigroup
  would not justify bounds on its actual `R` or `H_x`.

## Directly retrieved file blobs

These are Git blob IDs returned by the connector at the pinned commit. They
record exactly which detailed files were inspected; they are not claimed as a
new verification of the Lean development.

| Repository file | Blob ID |
| --- | --- |
| `NSP14/Width/AntipodalComparison.lean` | `96f375a72cd2d3fb2e1928b2afba17f620cccb68` |
| `NSP14/Width/IntegerPayment.lean` | `59339c0fafc6cce41b25e1d412f6534bfe1f5523` |
| `NSP14/Width/EdgeHoleCounting.lean` | `7e2cb3a5efaf2f3d8ee15c07ae5cd3059d80a297` |
| `NSP14/Width/EdgeHoleComparison.lean` | `7e3f594711e269ab6bb8b006ce3866b6ab669f6a` |
| `NSP14/Width/DenseLexResources.lean` | `bf4f679439ac142efcc66b6505654094c35dd9a0` |
| `NSP14/Width/DensePayment.lean` | `237b797fc3f093dc5755ddb653c7c55363907251` |
| `NSP14/Width/HigherFromSecond.lean` | `f27f61f5c501302551f7186ad30f196bf7a2b943` |
| `NSP14/Width/SparseComparison.lean` | `dcd1c50089506bb73411f1ecbbd7f7c971338fc5` |
| `NSP14/Width/FiveSmall.lean` | `b568a993a0e7e47c321380533953461779acf9a7` |
| `NSP14/Width/FiveHigher.lean` | `6c7ec730ac6ccc45649c9efdba6493ba284d8a9e` |
| `NSP14/Width/AntipodalCore.lean` | `15e8da59887c3233a14acc278a7d045259a1128e` |
| `NSP14/NarrowFour/Distance.lean` | `9590c37382a7da463d5af86d850c42550d3986a3` |
| `NSP14/NarrowFour/SocleTriangle.lean` | `d088d8b41a34c8ab0880d021957d4c8343132e09` |
| `NSP14/NarrowFour/StandardWords.lean` | `79a82759e765b605edbf353613ac9ff2684b0c8f` |
| `NSP14/NarrowFour/CubicPayment.lean` | `45e2616424ecbb1ee8c8b010ff3082ee3206508d` |
| `NSP14/NarrowFour/HigherRows.lean` | `4d9ca643830a7994febe4327ed02ec07aaf278a3` |
| `NSP14/NarrowFour/FirstCount.lean` | `9f200ae72d4bef3c72ad78d8bc9e8f44cbbeb93b` |
| `NSP14/NarrowFour/SmallWidths.lean` | `a664c9431bc26949ef4b13bfbaf510437b2f5420` |
| `NSP14/NarrowFour/WidthFourCompetitors.lean` | `943138adadd1e19b468d02b887cf5b2fabf70459` |
| `NSP14/NarrowFour/WidthFourInitial.lean` | `a60c3b61b9b616c714b51d46b9cc43f4ad198214` |
| `NSP14/NarrowFour/WidthFourComparison.lean` | `a119429b839dc2ef8d1b27689486e3197db38ac4` |
