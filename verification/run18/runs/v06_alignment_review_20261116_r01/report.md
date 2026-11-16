# V06 Lean経路同期 最終レビュー

**V06_ALIGNMENT_COMPLETE — Critical 0 / Important 0 / Minor 0。**
2026-11-16（JST）。対象はV06の五経路同期。既存Run18六契約を維持し、N4／Run19／全P14の完成には広げない。

- 開始base：`a7504eea25f02728d1be6cd0082e8484d639dbe2`。
- 固定proof：`d446fc2f18f7a8603d1eedd446e93810dc44d01c`。
- 完了証跡・独立実行レビュー対象：`0880f6f30836873036b4d9908b7dcef50125d2c8`。
- 289チェック・273 fixtureすべて成功。project 684 module（umbrella込み）をcold再構築、固定mathlib cacheは共有。
- 17 moduleのnormal/explicit型、10,713宣言の推移公理、base公開宣言70件の両型一致を確認。許容公理はpropext/Classical.choice/Quot.soundのみ。
- 既存証跡7,518ファイルとbase全8,998ファイルの規則内保存を確認。新negative controls 24件に加え、親担当の実CLI拒否試験3件も成功。
- 実測1726.788秒は検証コマンド合計（約28分47秒）。作業全体や独立レビューの所要時間ではない。

## 五項目の接続

| 項目 | 新経路からactual consumerへ | 凍結受入 |
| --- | --- | --- |
| endpoint | 全j witnessとforbiddenStart_height → competitorMin_height / competitor_zero_column → 元のRhat/RowPackage | 既存全幅consumer、W_CLOSE |
| antipodal第一行 | antipodal_integer_payment → actual_antipodal_first | W_FIVE / W_CLOSE |
| non-antipodal第一行 | nonAntipodal_integer_payment → actual_five_nonAntipodal_first | W_FIVE / W_CLOSE |
| higher | higher_capacity_from_second / actual_resource_envelope_add → actual_higher_from_second → five/sparse | W_FIVE / W_SPARSE / W_CLOSE |
| dense | 一つのL/Kを返すdense_core_lex_bound_two_branch + dense_payment_two/ge_three → actual_dense_firstterm | W_DENSE / W_CLOSE |

全五項目がconsumerまで接続済み。RowPackage/SocleBounds/Width.Closureの個別import閉包からStoppingが除かれ、旧有限計算枝はStoppingを保持する。actual全j核、PC/PG補償、元向きR/Hx、任意体、literal completion、各環自身の最小変数、全行を保存した。根別検査は直接参照とimport閉包の検査であり、推移的な数学は下記独立ソースレビューが補う。

## ファイル・再現・証跡

改変旧productionはEndpoint4＋Width7、新productionはIntegerPayment/HigherFromSecondの2。全ファイルの有限許可リストは[変更規則](../../../../docs/V06_ALIGNMENT_CHANGE_POLICY.json)、公開補題と原稿差分の詳細は[対応台帳](../../../../docs/V06_ALIGNMENT_LEDGER_JA.md)。既存公開型を削除・弱体化していない。旧verifier/checker・acceptance・証跡・ZIPは不変。

[全実行結果](../v06_alignment_20261115T152000Z_r01/verification.json)と同ディレクトリのSOURCE_SHA256/MANIFEST_SHA256/COMMAND_MAP、raw log、base/current declarations、audit_coverage、routes、alignment_controlsが固定proofと結び付く。再現には固定proof commitをcheckoutし、専用verify_v06_alignment.pyを使って未存在の別出力先を指定する。旧verify_run18.pyのガードは緩めていない。

親担当の独立checkerと別レビュー担当が別々のコードで同じ結果を得た。後者は親checkerを読まずに照合した。以下に数学・検証器・実行証跡の独立レビュー全文を収録する。各担当の除外範囲を他担当と親照合で補い、未解消の指摘・pending・declinedはない。

作業中のwork更新306df7bはRun19計画等5ファイルのみでLeanとの重複はなかった。公開用ZIPはこの固定proof/evidence/reviewの一致を確認して作る。最新workへの統合は別receiptで同一Lean/script/pin/evidenceと当該Run19更新の保存を確認し、固定snapshotの認証と区別する。


---

## 独立数学ソースレビュー

# Independent V06 mathematical source review

Review baseline: `a7504eea25f02728d1be6cd0082e8484d639dbe2`.
Workspace: `/tmp/ns-p14-v06-alignment-20261116`.
Proof commit: `d446fc2f18f7a8603d1eedd446e93810dc44d01c`. All 38 reviewed SHA256 hashes below were independently compared against both this committed tree and current worktree bytes and matched. A later commit is covered only if those contents match.

## Result and scope

Static mathematical/source review: **0 critical, 0 major, 0 minor findings**.

Reviewed all eleven modified production modules, both new production modules, all four new mathematical boundary fixtures, the named-root reachability fixture, umbrella append, and the supporting sources listed below. Read the full supplied order, implementation plan, and finite change policy. No AGENTS.md was present at applicable searched paths. Review was independent of implementation-agent success claims.

This is not Lean elaboration or full evidence verification. I did not build, run Lean, modify shared cache, check out, or commit. The only write is this report outside the worktree. I did not validate verifier/package/negative-control implementation, source/evidence manifests, raw-log authenticity, allowed transitive axioms, or compiled normal/explicit export equality. Those require the separate infrastructure review and verifier. Source inspection found no added mathematical axioms or `sorry`, `admit`, `sorryAx`, or `native_decide` in the seventeen changed/new mathematical Lean files. The named-root fixture adds only imports and #checks. Its explicit FiniteSocleBounds import was reread after the parent corrected reachability of competitor_zero_column; this affects the fixture only, not the three production import-closure roots.

## Mathematical and route conclusions

| Route | Source review |
| --- | --- |
| Endpoint | `competitorMin_height` directly destructs the original all-positive-j `competitorFiber` witness, reduces its actual long-side point with `exists_minimalFiber_le`, uses coordinate inequalities from `forbiddenStart_le`, and identifies the forbidden start by `Minimal.eq_of_le`. The final `minimalPoint_height` / `forbiddenStart_height` bound uses j>=1 without a stopping theorem or coprimality of m,u. `competitor_zero_column` takes j=u and coreHeight<=u-2, then uses the same carry_u/minimalFiber_budget resources. The signed-then-clamped definition and exact `actualDeadFiber_eq_inter` are unchanged. |
| Antipodal first row | `antipodal_integer_payment` proves the rational strict next-integer gap uniformly for h>=4. The actual consumer retains its exact statement and actual core/endpoint bound, weak surjective actual coreP bound, QCore first-third estimate, original R+2h<=W and W<=h^2. There is no h=4/5 split or call to `five_wordVolume_eight`, exact presentation/P/W formula, or Betti transport. The weak bound's normal-form/surjective-basis proof was read; it does not require t to be a unit modulo 2h. |
| Non-antipodal first row | One rational integer-payment lemma handles u>=8 using the original fourth-volume estimate and the existing mod-3 volume remainder. No u=8..11 refund branch remains in the actual first-row proof. Retaining the volume remainder's own residue arithmetic is consistent with the order. |
| Five/sparse higher rows | `higher_capacity_from_second` assumes the same rational B's row-two capacity inequality, not an actual beta2 conclusion. It divides only by positive choose(e,2) and choose(e,i), including i=e. The actual wrapper obtains the additive package from `actual_positive_rows_add`, uses the same B for coreP and Rhat+u, and uses Pascal over rational casts. It does not call actual five/sparse higher or a final comparison. Five uses B=14 at u=8 (resource row-two demand 104<=112), B=u^2/4 at u>=9 with the exact positive cubic gap, and preserves source vanishing above five. It does not call either choose-quadratic theorem. Sparse passes B=W and the existing `sparse_second_payment`; `actual_sparse_resource_add` is retained unchanged. |
| Dense | The new helper chooses one lex quotient L and one K, then simultaneously returns every positive core-row bound and the t=2 / t>=3 correction implications. Its quantified t<=q range still includes t=0,1. At t>=3 it uses r=t uniformly, not a t=3-specific correction. The gamma/coefficient proof includes q=4,t=3 with non-strict comparison. The new payment calls neither old payment nor old large-coefficient lemma; its proof never divides by a possibly-zero binomial. The actual consumer directly calls the new same-K helper and the new two payment branches. Old public resource/payment/coefficient statements are retained as compatibility exports. q=3 resources are unchanged. |

All actual consumer statements retain arbitrary `(k : Type) [Field k]`; divisions introduced by the new arguments occur in Q. Internal core variables `D.a` and full variables `D.Variables` remain distinct. Existing normalization/comparison chains still end at the same actual completed source and literal interval-completion target, each with its own `AtomExponent`. First/above-top handling remains in the existing all-row comparisons. The frozen W_FIVE/W_SPARSE/W_DENSE/W_CLOSE chains were read through their unchanged closed-goal proofs; this is a source connection observation, not a claim that frozen fixtures were rerun.

## Compatibility and import checks

A read-only source-header comparison against the baseline found all **57 baseline declarations** in the eleven modified production files present with identical comment/whitespace-normalized statement headers. Their enclosing variables and namespaces are unchanged in the diffs. This is a static statement-preservation check; compiled normal and explicit types remain verifier scope.

An independent recursive traversal of source import lines found:

- RowPackage: 477 reached module names, no Endpoint.Stopping.
- SocleBounds: 401 reached module names, no Endpoint.Stopping.
- Width.Closure: 715 reached module names, no Endpoint.Stopping.
- FiniteCompetitors: 416 reached module names, includes Endpoint.Stopping intentionally.

Traversal stops when an imported module has no local source; module counts include those terminal names. The two new production modules are explicitly appended to the umbrella with the old umbrella prefix preserved. HigherFromSecond's imports go down to NormalizedCapacity and PositiveRows; neither actual higher consumer nor final comparison is imported back into it. Source-level root checks and supporting proof-body reading were kept distinct from import reachability and axiom checking.

`audit/run18/RequestedGoals.lean` SHA256 is the required `86a0a18eff0632cb915d67748dcef47a88991cebf287ef95750f58b450bea689`.

## Exact boundary fixture coverage

- Endpoint: literal all-positive-length equivalence, unrestricted j witnesses, finite minima/height/pure-v API, small-height boundary, retained finite computational API, and m=6,u=3 noncoprime example with j=37 beyond the stopping bound.
- Integer payment: APD h=4 actual first row; APD h=5,t=2,u=10 with an explicit nonunit check; actual statements over arbitrary fields plus Q/F2/F3 instances; arithmetic first-row examples including all four formerly split non-AP widths.
- Higher: e=2,u=2,B=2; e=5,u=8,B=14; e=5,u=9,B=81/4; each quantified over all rows 2..e and explicitly instantiated at the top row.
- Dense: gamma=0 and payment equality at q=4,t=3,j=0; new payment on all rows through j=5; general j=q+1 top row; actual q=4,t=3 top row over arbitrary fields; same-K helper statement preserving the full t<=q quantified range.

These fixture bodies directly exercise the intended lemmas/consumers. Their existence and meaning were reviewed; no execution success is asserted here.

## Reviewed content hashes

Hashes were computed from the reviewed bytes after dense/higher implementation agents had completed. Any changed listed file requires renewed review or an explicit determination that the changed scope is outside this report.

| File | SHA256 |
| --- | --- |
| `NSP14/Endpoint/CarrySums.lean` | `9ae46d0698db6b8222d4f01dddd4348087fff6bc722d2a7b9c863540dce90652` |
| `NSP14/Endpoint/CompetitorBounds.lean` | `5265a086da0725401d61e5bf53224e1ebc3a05b006be4503bb6b83c62b6c8434` |
| `NSP14/Endpoint/FiniteCompetitors.lean` | `321449ac5b14fd26300c24835b255f30c02cc7d0e810f78f3b5b57fc351cfe03` |
| `NSP14/Endpoint/FiniteSocleBounds.lean` | `93ca2260b37fcdfbaf75554be0b440e1ec922bf2fc30ce105aa78847169c810d` |
| `NSP14/Width/AntipodalComparison.lean` | `a40398b76d2cb496b4560ccd3f14dc94ddf37465a0b06f6418660b3d64497ebf` |
| `NSP14/Width/FiveNonAntipodal.lean` | `4c7c11d7607edc96c3941a828a9f74a6af1ffbdb75fa2ac3abec7355ea32a2d9` |
| `NSP14/Width/FiveHigher.lean` | `436d9a80d69bc7f3155928a61c99878186fa2b6aa4056ad64043efd1652218e7` |
| `NSP14/Width/SparseHigher.lean` | `a704ea674e854d22c0834eb3fa17f3c993c0e03df4c1cbe6bdcc20950442db62` |
| `NSP14/Width/DenseLexResources.lean` | `9bdb0a81d44f6cd5d17986ac02ebc691193051d80e2738177395388b8f993dfc` |
| `NSP14/Width/DensePayment.lean` | `b529aedf9436a619b4377fc71865e2d4291f2e0d83c19994dfd2d8f15aeb3b5a` |
| `NSP14/Width/DenseComparison.lean` | `7de7522543967f98568924765c2351fbbf599b75340f1bb29762e3d977a165ab` |
| `NSP14/Width/IntegerPayment.lean` | `f7def4a993c944eb676615fa169d73655798fe2731723f2eb0cf240c8b49a9f5` |
| `NSP14/Width/HigherFromSecond.lean` | `a4126435ebc5829e99c0404dd0082bbff0b473ea43c7fd710adf368e3304b0a8` |
| `tests/V06Endpoint.lean` | `588ad3b1f7583cb552d8351960eddc128b90ebc22f707dd684fa7028345418f0` |
| `tests/V06IntegerPayment.lean` | `8151aa47eb6b83224591c11e9d78abff3be92b606b317bb9559739476a8db5fb` |
| `tests/V06HigherFromSecond.lean` | `5165c893c8dabdfc92d98520f95e149ee120e40079784badf220b7d487832398` |
| `tests/V06Dense.lean` | `747db30695235e0db7784b667adf46273d05a12b0159bcbb645451966dcb4423` |
| `audit/v06_alignment/RouteChecks.lean` | `7ed0a323b3cc793e10b47c2b847439747466a6c012d0f647730c86913e810418` |
| `NSP14.lean` | `8728efd06c8d891d29557ff62435e71e607ac80ec227589b860d4acc8fdbbf17` |
| `NSP14/Endpoint/ActualKernel.lean` | `9fcb8b751d540d92bd3d0c729109ad1001af913fc44a410d6b74150ad78c9c43` |
| `NSP14/Endpoint/Carry.lean` | `95ba789f8bcdb85db4e7cec6072cf197f1eec1ba532163180d0c8e932d9d0702` |
| `NSP14/Endpoint/PositiveRows.lean` | `ddfe975206ebe65cd579341a3a0a3127295667018b459f4be69a941efe66b9d1` |
| `NSP14/Endpoint/FullTransfer.lean` | `dbe038aa0960263c5008666a5f64dd184220af04a907b019baf37139b2f784f1` |
| `NSP14/Width/AntipodalCore.lean` | `ceaf178f71301a50e6eb3c7ea67d33bee8bad9253d54e1097e62e1a51bc4b80a` |
| `NSP14/Width/FirstResources.lean` | `0d61ddbb80751d3fb6273a62a587a85d2d9717d720cbf57d74741b069089631b` |
| `NSP14/Width/SparseSecond.lean` | `1137372080d07abd9fdbcbfa5827582f283ab383be2792cb24342a94cd917284` |
| `NSP14/Width/NormalizedCapacity.lean` | `001e46887db4c6dfcbc42407dcaed3f27fffcb6705fe40045a6b2574a842de0a` |
| `NSP14/Width/SparseComparison.lean` | `ebe3c2639fa6f01cf86033d0bd23fe0debc022db93bc5ad7108d0c826a9fb15b` |
| `NSP14/Width/FiveComparison.lean` | `07b81150019d368b326bd5447bb89be049ae21e8321f3b8183a6f7d9ae0ff524` |
| `NSP14/Width/Closure.lean` | `23d29bc36ddf482a291d8f81e7f9af9fc28426f7448e47a65c348931876592b0` |
| `audit/run18/RequestedGoals.lean` | `86a0a18eff0632cb915d67748dcef47a88991cebf287ef95750f58b450bea689` |
| `audit/run18/FiveClosedGoals.lean` | `cdc1809aca59375f9584a6d140e6124f250d69c528306b5a3934ba1561f0c71f` |
| `audit/run18/DenseClosedGoals.lean` | `ed572df4b0df76578b3f70678f34ca7a1b0948f63247bfe3f9f961eda1ab34af` |
| `audit/run18/PartialClosedGoals.lean` | `246d6f440927bfb3f96377f056ef7b54e757a004fe0456940ecc5712c3a58f0c` |
| `audit/run18/ClosedGoals.lean` | `383de8790d28cb0209d355196999ac5c1d1247802e7b93038081b25c306e51db` |
| `docs/superpowers/specs/2026-11-15-v06-alignment-order-input.txt` | `51372b807584acf3cd78d0b022a44658e4bfcdb6ae51db41aaeb43a448dfe66c` |
| `docs/V06_ALIGNMENT_PLAN_JA.md` | `82416a7eaec1181bb1aa5f88fc89b8b9923d097e98970331d24b30c0e71fffdc` |
| `docs/V06_ALIGNMENT_CHANGE_POLICY.json` | `876e70e3508007cc97d0fe887fdf8c08ccf5510095ba5142f93ae0ebcee798cf` |

---

## 独立検証基盤レビュー

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

---

## 独立実行証跡レビュー

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

---

## 親担当の独立照合（機械結果）

```json
{
  "status": "PASS_INDEPENDENT_V06_EVIDENCE_CHECK",
  "proof_commit": "d446fc2f18f7a8603d1eedd446e93810dc44d01c",
  "checks": 289,
  "fixtures": 273,
  "source_files": 1497,
  "manifested_evidence_files": 317,
  "inherited_evidence_files": 7518,
  "inherited_base_files": 8998,
  "declarations": 10713,
  "typed_modules": 17,
  "unchanged_base_public_declarations": 70,
  "cold_built_project_modules": 684,
  "route_roots": 13,
  "negative_controls": 24,
  "command_seconds": 1726.788
}
```
