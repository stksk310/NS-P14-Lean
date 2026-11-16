# Run19 public guard fix — independent static review

Verdict: **PASS within the scope below; no Critical, Important, or Minor findings.** This is a read-only code review, not a GREEN execution result.

Reviewed baseline: `/workspace/NS-P14-Lean-run18`, HEAD `07fe1ed952ae31ce01255ce53df538bf0a76d5cc` (confirmed by read-only `git rev-parse HEAD`). Reviewed proposals are outside that repository:

- `/tmp/run19-package-reviewed-source-fix.py`, SHA-256 `d3052ee904fc5336172b5b1fd7cbf71382faad17e33e70756eb8494516b99f90`
- `/tmp/run19-check-guards-regression.py`, SHA-256 `4f4e10d7ec884a24469a299a337ea8dcde46207ac40d30913a61972d8c5c5e72`

## Scope and reasoning

The packager diff adds only the three-line reviewed-source comparison at proposed lines 31–33. Before that comparison, `verify.check_source_manifest(root, source, proof)` already establishes that the manifest equals the current source content and fileset, and that each manifest digest matches the proof commit's Git bytes. The new comparison independently reads each same path from `reviewed_commit` and requires its SHA-256 to equal that digest. Thus acceptance requires each certified source entry to agree across current files, proof commit, and reviewed commit. Checking the exact Git bytes avoids reliance on a restored working tree or merely on the review receipt's asserted proof identifier.

The new loop is after the existing reviewed-commit ancestry check and before the existing reviewed-evidence checks. It leaves evidence, report, review-commit, archive-name, exclusive creation, ZIP CRC, and bundle hash gates intact. Missing reviewed paths cause `git show` to fail closed through the existing CLI's `CalledProcessError` handling. Source names and digest values have already been checked against the current manifest, including safe-path checks inherited from the verifier. The comparison uses the same Git access and SHA-256 conventions as the existing proof-source binding.

For inputs whose certified source entries already agree with the reviewed commit, the loop introduces no payload, metadata, archive-format, or output-path change. The R03 binding result in `/tmp/run19-audit-actual-bindings.json` reports all 1,581 source entries matching both commits; the corresponding read-only audit script explicitly checks those comparisons. This supports compatibility for R03, but I did not independently execute that audit or the revised packager and do not claim runtime acceptance here. A future source edit to the real packager/checker is itself manifested source and must be incorporated into new certification and review evidence through the normal flow; old evidence cannot certify newly edited source.

## Regression test assessment

The additional control at proposed checker lines 106–113 uses the real `pkg.checked_payload` function inside the existing disposable synthetic Git fixture. It creates a reviewed descendant with source B, restores proof source A in a later commit, then commits a receipt pointing to B. The evidence and manifest are unchanged in the B commit; `source_snapshot_commit` continues to name proof A; the review body and its hash remain valid; the reviewed commit is an ancestor; and the current receipt is committed at HEAD. The generated archive from the earlier positive case is under `artifacts/`, which is excluded from the source manifest, so committing it during this scenario does not invalidate the source fixture.

Consequently the negative case is nontrivial: current/proof source binding, reviewed evidence binding, ancestry, and committed review bytes can all pass while reviewed source differs. The assertion requires the specific `reviewed source Git bytes mismatch` rejection, preventing unrelated failures from counting as success. The earlier `valid_synthetic_publication_binding` and actual synthetic packaging remain positive controls and run before the new mutation. No later positive case depends on restoring the temporary repository.

The supplied `/tmp/run19_reviewed_source_binding_test.py` and its RED log demonstrate the same gap against the baseline packager: distinct A/B source digests, `accepted: true`, followed by the expected assertion failure. I inspected those files only; I did not rerun the reproduction.

## Boundaries and remaining validation

This review approves the minimum entry-wise binding requested: every certified source entry must have the same bytes in the reviewed commit. It does not establish equality of the entire historical Git tree/fileset, authenticate a reviewer, or prove what a human actually inspected. Those are outside this change and the supplied requirement. SHA-256 collision resistance and the pre-existing Git/object/manifest trust boundary remain unchanged.

No build, checker, Python proposal, reproduction, packager, or certification command was executed. No repository source, HEAD, evidence, or cache was modified. Only this report was written under `/tmp`. GREEN execution of the regression suite and revised-packager positive/negative cases remains the coordinator's post-cold-validation step.
