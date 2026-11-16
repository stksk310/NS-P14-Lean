# Run18 final publication-binding review

Verdict: **PASS** for the committed publication inputs at `c97fa324d90277bcae20a88863366bff6ba7a35b`.

Unresolved findings: **Critical 0 / Important 0 / Minor 0**. Pending: `[]`. Declined: `[]` within this publication-input review. Two stale metadata fields were found and corrected during review, as recorded below. This verdict does not certify a future publication decision, ZIP creation, Push or remote state.

## Exact scope and bindings

Reviewed evidence/document HEAD: `c97fa324d90277bcae20a88863366bff6ba7a35b`. Frozen mathematical proof source: `a5f480c5136042597fceae23ad06d2ef3923ed02`. R16 directory: `verification/run18/runs/release_candidate_20261115_r16`.

This is the publication-binding continuation of the completed independent mathematical/source/R16 review. I performed read-only Git, file-content and SHA checks. No Lean/build/checker execution, repository/index/HEAD/cache mutation, implementation, evidence rewrite or additional agent was used. Only this report was written. The working tree was clean at final verification.

All 2,033 SOURCE_SHA256 entries were independently rehashed again and matched both their proof-source Git blobs and reviewed-HEAD Git blobs. All 297 evidence-manifest entries were independently rehashed again and matched reviewed-HEAD Git blobs. The evidence key set exactly equals the files in the R16 directory except MANIFEST_SHA256.json; that manifest itself also matches its committed bytes. The previously reconciled full environment/types/axioms and retained evidence therefore remain bound to exactly the reviewed bytes.

The complete proof-source-to-reviewed-HEAD delta has exactly 303 paths: 298 R16 evidence files including the manifest, the raw final review, its source-review decision, and the three unbound status/final-review/execution-ledger documents. There are no changes to proof sources, frozen contracts, scripts, dependency bindings, previous evidence, licenses or provenance. Thus the previous exhaustive source review, all prior retained evidence and append-only baseline checks remain applicable without rebuilding.

R16 verification.json still reports PASS_RUN18_COMPLETE_VALIDATION and run18_complete=true. All 280 commands have passed=true and exit_code=0. It records 268 fixtures, 10,662 declarations, 2,421 new declarations, 2,033 source hashes, 297 evidence hashes and 7,212 retained evidence files. Current status agrees with all six closed IDs `[W_SPARSE,W_FIVE,W_EDGE,X_BHP_EK,W_DENSE,W_CLOSE]`, empty unproved IDs and empty unproved assigned declarations. The completed source review establishes all six original frozen mathematical contracts; no partial-closure qualification remains.

## Review document and publication extras

`verification/run18/complete_review_20261115.md` is byte-for-byte identical to `/tmp/run18-complete-review.md`. `docs/RUN18_FINAL_REVIEW_JA.md` contains that complete report verbatim exactly once, along with current Japanese metadata and the original document preserved as history. The source-review decision references the exact raw report SHA, correct frozen source and R16 summary, zero findings and empty pending/declined/remaining lists.

The final-review document is an explicit fixed extra in scripts/package_run18_audit.py:66. Therefore the proposed final decision must use review_report=`docs/RUN18_FINAL_REVIEW_JA.md` and the exact hash below. The report is then both the hashed decision target and an included payload entry. This avoids referring only to an optional raw report that is not automatically included by checked_payload. Its exact ZIP entry/hash still must be observed after packaging.

All three document extras, NSP14/Additive/Kneser_SOURCE_LICENSE and verification/run17/sources/provenance.json match exact reviewed-HEAD Git bytes. License and provenance also remain identical to the proof source. The current documents accurately distinguish the legacy finite five-checker PARTIAL note from authoritative R16 COMPLETE validation, and describe the ZIP as a reviewed proof/evidence bundle, not a standalone full-repository checkout. Reproduction uses the exact proof Git checkout and fixed dependencies. Historical intermediate partial reviews remain historical rather than being rewritten.

## Resolved metadata findings

Two minor stale current cross-references were identified in docs/RUN18_CLOSURE_STATUS.json: dense_global_proof_candidate.review_status (:531) still said PENDING_FINAL_COLD_VALIDATION_AND_REVIEW, and general_lex_existence_20261115.remaining (:505) still said final validation pending. The former was corrected in e75e4a0ac68ad18abfbb7039eab0f087ac0a2000; the latter in c97fa324d90277bcae20a88863366bff6ba7a35b. The execution ledger explicitly records both findings and resolutions. The R15 historical scope remains distinguished from the current R16 result.

The combined correction delta from initial evidence commit 3ad31806a26240e0671eb8e31888b48c9cfb0a51 changes only those two status values and the corresponding ledger notes. No bound source/evidence byte changed. A complete case-insensitive scan of the final status JSON has no remaining pending value. Both findings are resolved; final unresolved counts are 0/0/0.

## Exact SHA256 values

- R16 verification.json: `99b1c1d68b87d1e39bb94bfe93aa4a0d7ccd6fac8097f588c5a3722ac600c557`.
- R16 SOURCE_SHA256.json: `5b9b0ca17bcb02600b6028d1b184cb671524743c79226e3f69a1c98e6b421537`.
- R16 MANIFEST_SHA256.json: `1c5decbddcb9100223dfd9332dcdcf2d757b8240f7a6635b2abb2f3543b8d0d6`.
- docs/RUN18_FINAL_REVIEW_JA.md: `8c13a3a84d9969ecfb8069cce10e032d59994295a3a0a256b98f4da0b1f04bd2`.
- docs/RUN18_CLOSURE_STATUS.json: `988826218e5b11415f664cd63651e4b3590094fc6f4609644b0ad173684b0b74`.
- docs/RUN18_EXECUTION_LEDGER_JA.md: `b8f7ce068db02a5fbfabf060ec3adbef9bcb57a912eaf2b53f23db416bb8becf`.
- verification/run18/complete_review_20261115.md: `118131fb3151fdfbec20a175344114c67831dcdecf686dc758ea8fb977447df9`.
- verification/run18/review_snapshot_complete_20261115.json: `4594101c10a566c12d8412334acd85a7f1dbd290a530ac132e40ae2698e1f282`.
- NSP14/Additive/Kneser_SOURCE_LICENSE: `c71d239df91726fc519c6eb72d318ec65820627232b2f796219e87dcf35d0ab4`.
- verification/run17/sources/provenance.json: `2208cff48afa896a1cf44b565497d58285816f4a2f096646afdb8b5de396b82e`.

The proposed final publication decision may bind reviewed_commit to `c97fa324d90277bcae20a88863366bff6ba7a35b`, source_snapshot_commit to `a5f480c5136042597fceae23ad06d2ef3923ed02`, the summary/manifest/report hashes above, all six closed IDs, run18_complete=true, zero Critical/Important/Minor and pending=[]/declined=[]. This report approves those reviewed inputs; it does not assert that the future decision has already been created or checked. ZIP entry/hash/CRC, immutable-output behavior, authorized normal Push, remote SHA and post-publication clean status remain separately observable release operations, outside this completed input-binding review.
