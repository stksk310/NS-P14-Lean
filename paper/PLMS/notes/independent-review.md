# Independent manuscript review

Historical scope: this report reviews the first full draft. The subsequent
Navi-requested revision and its editing checks are recorded separately in
`navi-revision-response.md`; they are not represented as a new independent review.

Reviewed the English manuscript in `main.tex` and all seven `sections/*.tex`
files against the pinned source at
`stksk310/NS-P14-Lean@a5e122a4d09536b1609c5faa8d419f8faf81671f`.
Line references below refer to the integrated manuscript reviewed on
2026-11-16 and may move with later typesetting edits.

## Result

No unresolved mathematical correctness issue was found in the integrated
draft. Two concrete issues found during review have been corrected and
the corrections were checked in the files:

1. **False intermediate wording in the ordinary volume argument, fixed.**
   `sections/ordinary.tex:126`–`129` now says that the offset level cannot
   increase on arrival at an atom residue **after the first edge**. The
   qualification is necessary: the first edge from residue zero to an
   atom has levels zero and one. The original volume inequality was
   correct; the unqualified intermediate assertion was not.
2. **Undefined relative polynomial-ring notation, fixed.**
   `sections/ordinary.tex:195` now defines `R=k[x,E]` before the displayed
   `b_i^R(G)` spectral-sequence calculation at line 207.

The final one-hole passage at `sections/width.tex:77`–`110` was rechecked
after revision. It uses the combined actual-cone upper inequality, with
`P+delta <= q+3`, rather than needing a stronger separately exported
formula for all internal Betti numbers. For an interior hole `delta=0`;
for an end hole `delta=1` cancels the binomial part of the empty-block
correction and leaves both stated top-row indicators. Its use agrees
with the final proof route.

## Mathematical scope checked

- **Statement and conventions.** The theorem concerns total quotient
  Betti numbers, not individual internal degrees. Source and target use
  their own minimal generators. The literal target interval is retained,
  including the one-generator case. The distinction between physical
  width `du` and normalized width `u` is maintained throughout.
- **Common bridge and target.** The monomial-coordinate proof of the
  algebraic/completed tangent-cone bridge, scalar-extension descent,
  normalization hypotheses, minimal interval generators, exact capacity
  formula, its lower envelope, monotonicity, and the restricted ranges
  of the low-row estimates were checked. In particular, the third-row
  shortcut is not applied at width four.
- **Ordinary branch.** Checked the heads/terminals description; opposite
  jump filtrations rather than a global module isomorphism; jump bounds;
  one fixed Green cut; truncation generation and the exact tower;
  coordinate contribution intervals and resource counts; harmonic
  boundary minors; the signs in the partial-Euler exact-sequence and
  spectral-sequence estimates; the top relative row; the exact zeroth
  homology correction in the full transfer; target margins; small-rank
  and unbounded scalar arguments; Sidon exclusion of the exceptional
  corners; and descent to the original field.
- **Endpoint branch.** Checked minimality under `u<m`; the actual
  core-to-tangent-cone map; finite minimal fibers; the formula using
  **all** positive competitors; the intersection `M_s cap T_s` in the
  kernel; the finite generating argument without `gcd(m,u)=1`; the
  shortest-word volume and same-orientation height resources; the socle
  injection; the homology balance using finite homology rather than
  infinite chain Euler sums; actual quotient-kernel compensation; and
  the full-variable transfer retaining its torsion/top-row term.
  The internal two-variable socle and the endpoint socle remain distinct.
- **Width branch.** Checked the full arithmetic-progression exception,
  one-hole minors and correction estimates, dense prefix argument,
  single whole-Hilbert-function lex quotient and weighted child count,
  Vandermonde payment, second-row propagation, composite-order Kneser
  growth, sparse envelopes, five-generator short-width cases,
  the antipodal spanning bound, two-variable socle triangle,
  Savchev--Chen return to the original labels, four-generator high-row
  cubic reduction, small-width cases, and the remaining width-four
  normal forms and all-longer-competitor argument.
- **Small generators and assembly.** Checked the one- and two-generator
  presentations, the one-internal-variable endpoint resource argument,
  payment in each of its three rows, and the disjoint/exhaustive final
  case split. Zeroth rows, the possible source row `i=e`, and vanishing
  above the source embedding dimension are included.

The local Lean declarations in `Main`, `Main/Branches`,
`Main/Partition`, `Main/IntervalTarget`, `Ordinary/Closure`,
`Width/Closure`, `NarrowFour/Comparison`,
`SmallEmbedding/ThreeComparison`, `SmallEmbedding/LanTuVu`,
`ArithmeticSequence/BettiFormula`, and `Homological/Betti` were inspected.
The Run16--20 correspondence records and the ordinary, endpoint, width,
and semantic source maps were used for the finer declaration-level
connections. No additional linear Lan--Tu--Vu estimate, exact
antipodal presentation, general initial-ideal equality, or historical
periodic stopping theorem is required by the exposition.

## Independent arithmetic checks

A separate numeric reviewer used exact symbolic/rational arithmetic to
recalculate the sparse first-row gap polynomials, the quadratic distance
envelope, row-two factorizations, five-generator gap polynomials,
ordinary rank-three identity, all five small-rank seed-table rows, the
rank-nine seed, and the unbounded ordinary seed/shift/floor identities.
They agreed with the displays.

Additional finite checks passed for one-hole correction inequalities and
dense-width combined payments through `q=50`, propagation monotonicity
through `e=60` (widths through `5e`), four-generator high-row envelopes
through width 500, the displayed small-width capacity tuples, and the
width-four first-row residue table. These checks support the arithmetic;
the manuscript's general proofs, not the finite checks, establish the
unbounded assertions.

## Exposition and verification limits

The duplicate definition of order was removed, and the width section now
aliases the endpoint invariants instead of redefining the whole setup.
The remaining restatements of the endpoint working inequalities help
the width calculations and do not introduce competing definitions.

This review assessed the mathematical text and source correspondence.
It did not perform a fresh Lean compilation, reproduce the repository's
recorded axiom audit, or independently re-referee every cited external
theorem. Bibliographic verification and LaTeX compilation/layout checks
are separate recorded tasks. The paper should be delivered as a reviewed
research draft, without implying journal acceptance or external
peer review.
