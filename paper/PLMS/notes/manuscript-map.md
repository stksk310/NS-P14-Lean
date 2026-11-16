# Manuscript correspondence

All declarations refer to [stksk310/NS-P14-Lean at a5e122a4d09536b1609c5faa8d419f8faf81671f](https://github.com/stksk310/NS-P14-Lean/tree/a5e122a4d09536b1609c5faa8d419f8faf81671f).

| Article | Formal source | Details |
| --- | --- | --- |
| Theorem 1.1 | `NSP14/Main.lean`: `NumericalSemigroup.p14_totalBetti_le_intervalCompletion` | Every S, original arbitrary k, every i; actual completed tangent cones and separate minimal variables |
| Proposition 2.1, completion | `Semigroup/CompletedComparison.lean`, `Semigroup/FormalFactorization.lean`, `Homological/Presentation.lean` | Actual ideal powers and supported formal power series; monomial bases preserve actions |
| Proposition 2.1, scalar extension | `Homological/ActualCoefficientBaseChange.lean`: `actualG_totalBetti_baseChange` | Same-characteristic extension; actual ranks descend to original k |
| Proposition 2.1, normalization | `Semigroup/WidthNormalization.lean`, `Endpoint/Normalization.lean`, `Main/Partition.lean`: `narrow_parameters` | Original carrier, multiplicity and physical width retained |
| Proposition 2.2, target formula | `ArithmeticSequence/Interval.lean`: `interval_closure`; `ArithmeticSequence/BettiFormula.lean`: `completed_AP_totalBetti` | Target minimal width min(w,m−1), correction D=v−((m−1) mod v) |
| Minimum target capacity | `Target/APLowerRows.lean` and width consumers | Each capacity used only in its indicated range; third row requires v≥5 |
| Section 3 | [ordinary-source-map.md](ordinary-source-map.md) | Includes relative top row, exact H0 transfer and zero deficit |
| Section 4 | [endpoint-source-map.md](endpoint-source-map.md) | Actual intersection kernel; Q_C→Q_G compensation; distinct socles |
| Section 5 | [width-source-map.md](width-source-map.md) | Latest sufficient proofs, including new cubic and width-four all-m family |
| Section 6, e=1,2 | `SmallEmbedding/Base.lean`, `Semigroup/IntervalCompletionAll.lean` | Literal interval completion even at [1,1]; direct (1,1,0,…) two-generator profile |
| Section 6, e=3 | `SmallEmbedding/LanTuVu.lean`: `actual_one_rows`, `actualR_one_bound`; `SmallEmbedding/ThreeComparison.lean`: `three_comparison` | Uses actual pure-word injection and positive-competitor budget, not the original paper's stronger linear estimates |
| Section 6, exhaustive assembly | `Main/Partition.lean`: `parameter_partition`; `Main/Branches.lean`; `Main.lean` | Six disjoint regions and all homological rows |
| Source/target length example | `Main/IntervalTarget.lean` and exact AP formula | e(source)=4 gives beta5=0, ordinary target m=6 gives beta5=5 |
| Appendix A, semantics | [semantics-and-references.md](semantics-and-references.md) | Tor identification and all objects checked from definitions |

## Editorial decisions

The body presents mathematics in English, with one set of common reductions
and capacities and a short formalization appendix. Detailed declaration links,
release evidence, and historical proof changes are outside the body. The
ordinary, endpoint, and width sections were drafted independently, integrated,
and reviewed against the pinned sources. Internal numerical checks supplement
source inspection; they do not establish universal validity in place of Lean.

## Source status

Revision 2 adds Corollary `cor:width-bound` using the main theorem plus the
standard filtered-Koszul local-ring comparison and the exact interval upper
envelope. This consequence has no separately asserted Lean declaration.
See [navi-revision-response.md](navi-revision-response.md) for proof details,
the CMS/Pardue literature checks, and the one-hole scope correction.

The pinned Run20 completion record reports all P14 closed, no necessary
unproved mathematical inputs, and no unresolved review issues. The present
task does not claim a fresh kernel replay. The English prose itself is a
human-readable reconstruction and is subject to ordinary author/referee review.
