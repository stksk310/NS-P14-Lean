# Independent V06 infrastructure review — fixed source

Verdict: PASS_WITH_EXACT_SCOPE. Remaining critical / important / minor findings: 0 / 0 / 0.

Proof source reviewed: `d446fc2f18f7a8603d1eedd446e93810dc44d01c`.
Fixed BASE: `a7504eea25f02728d1be6cd0082e8484d639dbe2`.
Workspace read: `/tmp/ns-p14-v06-alignment-20261116`.

This is an independent static infrastructure/source review against section 6 of the saved V06 instruction and the fixed change policy. It does not certify a completed production run, a finished distribution ZIP, or mathematical proof-body dependencies. A separate evidence audit is required after the full run. All scoped working-tree bytes were compared with the exact proof commit. The entire 1,497-file source manifest was also checked against that commit.

## Scope and findings

- `scripts/verify_v06_alignment.py:25`: BASE, finite modified/new/append-only sets, toolchain/mathlib pins, frozen RequestedGoals hash, and allowed transitive axioms are explicit. Policy JSON is compared with constants. Read-only invocation of validate_changes passed against 8,998 baseline files; the allowed sets contain 11 modified files, 15 new files, and 3 append-only files. Inherited verifier/checker/acceptance/evidence/artifact bytes outside those sets remain fixed; additional outputs require the dedicated V06 evidence/archive prefixes.
- `scripts/verify_v06_alignment.py:71`: absolute, parent-traversal, backslash, escape, and symlink path components are rejected. Output directories must be unique dedicated V06 paths. Exclusive mkdir establishes output ownership; the failure handler at line 459 writes only after that mkdir succeeded. This resolves the initial existing-output failure-log race. Controls and routes use exclusive file creation; package uses exclusive ZIP creation.
- `scripts/verify_v06_alignment.py:164`: all tracked/new non-evidence sources, including scripts/docs/configuration, are manifested and bound to the proof commit. HEAD and source hashes are rechecked before and after commands. Old evidence is SHA256-manifested before execution and compared after execution. Source and evidence manifest functions compare both bytes and filesets.
- `scripts/verify_v06_alignment.py:183`: normal/explicit types and collectAxioms coverage apply to every audited declaration in all 11 edited old production modules, both new production modules, and the four declaration-bearing new fixtures. Every nonprivate BASE export of edited modules is required with identical two printed types. Genuine or self-dependent extra axioms are rejected; axiomInfo alone is correctly not treated as a new mathematical axiom. Import-only NSP14/RouteChecks coverage is checked using actual environment module metadata rather than fabricated declarations. This resolves the initial impossible declaration-row requirement for those two modules.
- `scripts/verify_v06_alignment.py:281`: BASE declarations are obtained from an isolated BASE source archive and build; optional donor sources/pins are checked before copying its build directory. The production run moves the whole project lib/lean and IR caches, which includes edited Endpoint modules and every downstream module, while retaining fixed mathlib packages. This is sufficient cache scope by construction; actual run results remain to be audited.
- `scripts/verify_v06_alignment.py:381`: all 280 R16 command identities are saved with old/new command lists. All old output and generated EnvironmentAudit paths are mapped into the new V06 directory; the 268 old fixtures remain present. Independent read-only fixture ordering produced 273 total fixtures. Commands are not silently dropped; package independently checks exact mapped command coverage against the immutable R16 inventory.
- `scripts/check_v06_alignment_controls.py:27`: new controls call the actual new verifier rejection helpers in a copied disposable Git tree, covering dangerous/existing/symlink output, disallowed inherited source/evidence edits, source/evidence bytes/filesets, missing old-module/declaration normal/explicit/axiom coverage, extra/self axioms, BASE export type/removal, declaration omission, and missing import-only modules. Existing Run18 publication guards are separately replayed and are not counted as new controls. The review read the control implementation; its production runtime log is outside this static report.
- `scripts/check_v06_routes.py:59` and `audit/v06_alignment/RouteChecks.lean:10`: per-root lexical direct-reference checks and individual import closures are explicitly distinguished from full transitive proof dependencies. Independent read-only check() passed all 13 named roots, all three Stopping-free main import closures, retained stopping-based finite computation, lower-wrapper import separation, and umbrella reachability. RouteChecks is a named-declaration reachability fixture. Full proof-body mathematics is delegated to the separate independent mathematical reviews; this report does not misrepresent the route checker as kernel dependency reconstruction.
- `scripts/package_v06_alignment.py:22`: publication requires the exact five-item V06 scope and independently reviewed verifier; source, evidence, review report, and manifest hashes must agree. Current source bytes must match proof/evidence/reviewed commits, every manifested evidence file and manifest must match evidence/reviewed commits, ancestry is checked, and review/report bytes must exist unchanged in publication HEAD. Declaration records are checked against raw audit rows, and all 280 command mappings are rechecked. Unique dedicated archives are created exclusively and CRC/fileset/content hashes are checked. Old Run18 COMPLETE metadata is not used as the new alignment authority. The initial missing new-archive allowlist exemption was fixed with a strict archive filename predicate.
- Policy, plan, ledger, handoff, and appended historical ledgers describe the finite scope, old proof/evidence preservation, static-route limitations, source/evidence/review binding, actual consumer connections, and exclusions for N4/Run19/all-P14. They do not claim that paper review or old Run18 evidence certifies the new Lean source.

## Independent read-only checks performed

All four Python scripts compiled in memory. The new finite-change validator passed. Exact current-vs-proof bytes were checked for every scoped file below; source_manifest/check_source_manifest additionally bound all 1,497 source files to the proof commit. The route check and fixture inventory/order checks passed as described above. This reviewer did not edit source, build, run Lean, change HEAD/index, alter shared caches, or write into verification/artifacts. Only this report and its temporary hash-binding JSON were written under /tmp.

## Exact reviewed hashes (SHA256)

- `scripts/verify_v06_alignment.py`: `5dae7e58e4250d89c991ecc9a33afaf7a87ada2e21c352a80ca58021a77e0761`
- `scripts/check_v06_alignment_controls.py`: `5600f335db8fa85d925f517ee012a6df808b22d6da59ed2a92392b34f6ec1ad1`
- `scripts/package_v06_alignment.py`: `2e94747759bbaa49e5f356ffaea0bbed16cbc1a95bce6b3e90756e176d43ea59`
- `scripts/check_v06_routes.py`: `1260ac20d897c9a0c90eba9b18c065017955a9f4cb042962929c8073d6ee555c`
- `audit/v06_alignment/RouteChecks.lean`: `7ed0a323b3cc793e10b47c2b847439747466a6c012d0f647730c86913e810418`
- `docs/V06_ALIGNMENT_CHANGE_POLICY.json`: `876e70e3508007cc97d0fe887fdf8c08ccf5510095ba5142f93ae0ebcee798cf`
- `docs/V06_ALIGNMENT_PLAN_JA.md`: `82416a7eaec1181bb1aa5f88fc89b8b9923d097e98970331d24b30c0e71fffdc`
- `docs/V06_ALIGNMENT_LEDGER_JA.md`: `9b65f4194790b2136e51a5426b4d8b33933310b82cf819c53c44ffd2a8b77743`
- `docs/V06_ALIGNMENT_HANDOFF_JA.md`: `cbd179149535cf81b02301dcb7f8b739febeae43b9b9d6f5a7527f2f964a6a7b`
- `NSP14.lean`: `8728efd06c8d891d29557ff62435e71e607ac80ec227589b860d4acc8fdbbf17`
- `LEAN_PROGRESS.md`: `c5e819ee5402f09ee94fdbbe616b0456204a1301812c862fafab657bbd3d1ff3`
- `docs/LEAN_PAPER_ALIGNMENT_JA.md`: `408beccaebf1f62e5afeff7a6892d533c0701a34c522d10f59a245ee277d7d1a`
