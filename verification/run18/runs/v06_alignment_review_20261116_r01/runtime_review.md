# Independent V06 runtime evidence review

Verdict: PASS_WITH_EXACT_SCOPE. Remaining critical / important / minor findings: 0 / 0 / 0.

Reviewed evidence commit: `0880f6f30836873036b4d9908b7dcef50125d2c8`.
Evidence commit: `0880f6f30836873036b4d9908b7dcef50125d2c8`.
Proof snapshot: `d446fc2f18f7a8603d1eedd446e93810dc44d01c`.
Fixed BASE: `a7504eea25f02728d1be6cd0082e8484d639dbe2`.
Run: `verification/run18/runs/v06_alignment_20261115T152000Z_r01`.

This independently audits the completed run and its stable Git evidence. It supplements, and does not replace, the separately saved infrastructure source review. I wrote and executed an independent read-only audit script, `/tmp/v06-runtime-audit-own.py`; I did not read or rely on the coordinator's independent-check script or result. All assertions in my script passed. Its machine-readable result is `/tmp/v06-runtime-own-result.json`.

## Findings and certification scope

No unresolved findings were identified in the reviewed runtime evidence.

1. All 1,497 manifested sources match their SHA256 values and the proof/evidence Git trees. The source fileset equals the non-verification/non-artifacts fileset at the reviewed commit. All 317 manifested run evidence files match their SHA256 values and evidence Git tree; the run fileset is exact, and MANIFEST_SHA256 itself matches the committed bytes. Proof is an ancestor of evidence.
2. All 7,518 inherited verification/artifact files are present at the stable reviewed commit with exact recorded SHA256 values, unchanged proof/evidence Git blob identities, and current bytes. All 8,998 BASE files remain present; every inherited file outside the finite modified/append-only sets retains its original bytes, and all three append-only files retain their exact BASE prefixes. Frozen RequestedGoals has SHA256 `86a0a18eff0632cb915d67748dcef47a88991cebf287ef95750f58b450bea689`. Extra committed files satisfy the fixed finite source/evidence/archive policy. The coordinator's later untracked review directory is outside this stable-commit fileset comparison and is not certified by this report.
3. All 289 check records have exit code 0 and passed=true; each corresponding raw log was read, including decompressed environment logs, and no warning marker was present. The final in-progress record equals the completed record. The 280 old R16 commands are mapped exactly to new outputs/generated audit input, with old commands retained in COMMAND_MAP; none was dropped or executed with old R16 output paths. All 268 old fixtures remain, and all five new fixtures are present, for 273 unique fixtures. Each has one recorded Lean command with `-j1 -M12288` and explicit output, and fixture imports precede their consumers. Total recorded command seconds are 1726.788.
4. The raw current environment audit has 10,713 unique declaration rows. Every saved row matches raw name/module/axioms/normal type/explicit type and original exported kind, and each declaration's source hash matches the source manifest. All rows have only permitted transitive axioms (`propext`, `Classical.choice`, `Quot.sound`), with no self axiom dependency. All 17 edited/new declaration-bearing modules have normal/explicit type coverage. Actual imported-module metadata covers these plus the two import-only modules NSP14 and RouteChecks. Per-module counts match audit_coverage.
5. All 70 saved BASE declarations match the independently generated raw BASE audit log exactly. Every BASE public export remains present with identical normal and explicit type. The BASE build succeeded in its recorded isolated workspace. The production/source pins, snapshot, mathlib manifest revision, and current shared mathlib Git HEAD agree on Lean 4.36.0-rc2 and mathlib `139105d28c7685a154cb3093f79edb2e16708099`.
6. All 24 new alignment controls have unique names and passed=true; each intended negative condition records its actual rejection, and the runtime log reports PASS with count 24. They are the new verifier's own controls, separate from the replayed legacy publication/axiom-policy checks. The control implementation and rejection paths were covered in the prior static infrastructure review.
7. The fresh-cache receipt records movement of the whole project lib/lean and IR caches, retaining shared mathlib. The raw build log finishes successfully with 6658 jobs and contains 684 distinct cold-built NSP14 modules, including every edited production module, both new production modules, RowPackage, SocleBounds, Width.Closure, and the umbrella. Thus the evidence includes edited Endpoint and downstream rebuilding, rather than only new modules or Width/Lex rebuilding.
8. Re-running only the read-only static route computation reproduces routes.json exactly: 13 named proof roots, three individual main import closures without Stopping, retained finite stopping computation, new-module umbrella reachability, and lower higher-wrapper import separation. These remain source/direct-reference and import checks, supplemented by the separate mathematical proof-body reviews. This report does not treat them as a reconstruction of erased kernel proof dependencies.
9. The summary retains exactly the five V06 alignment items and preserves inherited Run18 COMPLETE. It explicitly excludes N4, Run19, and all-P14 completion. This runtime review certifies the fixed proof/evidence pair above; it does not certify a future publication ZIP, later review-file commit, remote planning merge, or any future source change.

No Lean or Lake build was run by this reviewer; no source, Git index/HEAD, cache, or repository evidence was written. Only new audit script/result/report files under /tmp were written. The earlier source-only report remains unchanged.

## Exact evidence hashes (SHA256)

- `source_manifest_sha256`: `e7a238cd011c3969bcaa61517d9ad2f402ff69057cbdfa2c2c387891ddc465f3`
- `verification_manifest_sha256`: `9cacc74ddaa57d3b4fec633870faf2487fd2dae3c147e8e99bd49234266a5a6c`
- `verification_summary_sha256`: `6deca563b36fd2378b38dced54ecd68e561f761a31aaded95eb4050a5eb292fb`
- `raw_environment_sha256`: `72d61c9786f4518ae13557df420025d65b5d75a9cc61015ac61930172fde7993`
- `raw_base_environment_sha256`: `183cbd09ad32a98eeebf9ce4e014a4b631487f1948aeaa9e0292ace8304342af`
- `build_log_sha256`: `f0551f4042b4694635066dc0d3897e2ffec7ef3d7d59f7d7dacc32d710fab53a`
- `static_report_sha256`: `5433e2bca2367a48db2dbe807777fa0b7eb9bc4c9f0478c136acfbab83edc0a1`
- `independent_audit_script_sha256`: `387c737f023ae38f7291a22f4f198bdceb9d63dcbb818b99ef6175b1bda7a3b7`
- `independent_audit_result_sha256`: `ea00fa43c1a71d1e772827269fccde2819184249ebdff8faa97b09ee72a13fa6`
