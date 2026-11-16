# P14 English manuscript — PLMS preparation version

Title: **Betti numbers of numerical semigroup tangent cones and interval completion**

`main.pdf` is the compiled English article (25 pages), including author details,
the AI Declaration, and publication/reproducibility statements.
`main.tex`, `sections/`, and `references.bib` are the editable sources.
Build with `latexmk -pdf -interaction=nonstopmode -halt-on-error main.tex`.

The manuscript follows `stksk310/NS-P14-Lean` at commit
`a5e122a4d09536b1609c5faa8d419f8faf81671f`. Source inspection uses final
Run16–20 correspondence when it supersedes the older Japanese V06 exposition.
The 27 reference files in `sources/` were checked byte-for-byte against the
Git blob identifiers in `notes/SOURCE_SNAPSHOT.json`.

## Reading and correspondence

The article gives the mathematical proof; Appendix A identifies the formal
statement and pinned development. The detailed correspondence is separate:

- `notes/manuscript-map.md`: overview and common/small-generator statements.
- `notes/ordinary-source-map.md`: the fixed cut, tower, and numerical inequalities.
- `notes/endpoint-source-map.md`: all competitors, the socle resource, and compensation.
- `notes/width-source-map.md`: narrow-width cases and final proof replacements.
- `notes/semantics-and-references.md`: actual Tor/complete-ring semantics and verified bibliography.
- `notes/independent-review.md`: first-draft independent mathematical review and corrections.
- `notes/navi-revision-response.md`: width corollary, one-hole quantifiers,
  expanded explanations, and references added in response to the Navi audit.

## Status

This is a PLMS preparation version for author review, not a submitted
or published article. The sole author is Keisuke Sato, Independent researcher,
Japan; contact and ORCID are included in the article. This drafting task inspects the pinned Lean declarations
and archived completion evidence; it does not rerun the entire Lean project.
Fresh checks of the manuscript cover LaTeX compilation, internal references,
bibliographic keys, exact source hashes, and the reviewed mathematical formulas.

`submission/cover-letter.txt` is the draft cover letter.
`submission/author-metadata.json` records the author-supplied facts, MSC codes,
and an editor suggestion. `submission/PLMS-checklist.md` distinguishes prepared
materials from pending final checks; `submission/reproduce-lean.md` gives the
release-prescribed clean replay procedure. A fresh full Lean replay and a new
final mathematical audit are not claimed by this preparation step.

No new mathematical claim stronger than the required final Lean contracts is
needed: in particular, the one-hole argument uses sufficient rank bounds, and
the five-generator antipodal argument uses a spanning bound. Source and target
always retain their own minimal polynomial rings, the physical width remains
`d*u`, the coefficient field is arbitrary, and the upper source rows are kept.
