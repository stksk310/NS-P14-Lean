# Run18 COMPLETE：六ID・最終検証・独立レビュー

六つの元の凍結契約をすべて閉鎖した。未証明の担当ID・未解決のレビュー指摘はない。全域P14のRun19/20まで完成したという意味ではなく、Run18の五生成元以上・全物理狭幅と一般BHP/EKの担当範囲を完成した。

- proof/source snapshot: `a5f480c5136042597fceae23ad06d2ef3923ed02`
- [最終cold検証R16](../verification/run18/runs/release_candidate_20261115_r16/verification.json): **280 command／268 fixture、10662宣言／新規2421宣言**。全check PASS、指定宣言不在のexpected-openは0。
- source 2033件、evidence 297件の全hashを保存し、既存証跡7212件のbytesを保持。通常型・explicit型・推移公理・自己依存・Git bytesを照合した。許容依存は`propext`・`Classical.choice`・`Quot.sound`のみ。
- verification SHA256: `99b1c1d68b87d1e39bb94bfe93aa4a0d7ccd6fac8097f588c5a3722ac600c557`
- 閉鎖: **X_BHP_EK・W_EDGE・W_DENSE・W_SPARSE・W_FIVE・W_CLOSE**。`NSP14.Run18.all_closed`が元の六Propの連言を証明する。
- 独立コードレビュー: **Critical 0 / Important 0 / Minor 0、pending=[]、declined=[]**。既存レビュアー`/root/run18_edge_review`が追加sourceと最終証跡をread-onlyで照合した。新規のfresh reviewerを起動したという表示はしない。

今回の最終追加はactual cyclic QCのhomogeneous kernel/Hilbert/変数relabel、同じ一つのlex商と同じK、prefix生成元再帰・suffix harmonic評価、dense第一項支払い、全物理狭幅のliteral completion比較。係数体は任意で、元のR・V=d*u・双方自身のactual最小変数を維持し、CM・P_C=P_G・d=1を前提にしない。全行には0、sourceの上端と消滅後、target自身の上端を含む。

公開scope補足：R16内の`five_checks.json`に残る旧generatorの「Run18 remains PARTIAL」は、その有限five-checker checkpointの履歴注記である。現在の全六IDの判定はR16のCOMPLETE結果とこの最終レビューを用いる。boundな旧checker/logは書き換えない。ZIPはレビュー済み証明・証跡bundleであり、継承script一式まで含む独立実行可能なrepository全体とは表示しない。再現時は上記proof/source commitのGit checkoutと固定依存を使用する。

原稿の一部の強い中間等式は、対応表に記録した十分な別証明で置き換えた。凍結した六出口を弱めていない。有限checkerは普遍Lean証明の代わりにせず、Q/F2/F3の実例と176946支払いを補助検算として扱う。

公開判定の`review_report`は、以下の独立レビュー全文を含む**この文書そのもの**を指す。COMPLETE ZIPはこの文書の正確なbytes/hashを含む。ZIP生成・上書き拒否・全entry/hash/CRC・通常Pushとremote SHAは別の公開receipt/実測で確認する。ここでは未実行の公開成功を先取りしない。

## 最終独立レビュー全文

# Run18 all-six closure — independent review

Verdict: **PASS — all six original Run18 mathematical contracts and completed R16 verification**.

Critical: **0**. Important: **0**. Minor: **0**. Pending review items: `[]`. Declined-to-judge items: `[]` within the assigned source/proof/evidence scope. No unresolved mathematical, contract, validation or source-binding findings remain. All six IDs are closed; this is not a partial proof checkpoint. Final publication operations are assessed separately below.

Reviewed frozen proof source `a5f480c5136042597fceae23ad06d2ef3923ed02` against certified R15 source `6074994621ca5b57be28d44729a8ebab46f700a6`, following published checkpoint `19644d31f5948002fcac1fce28e746e2b2918cf0`. This is a continuation of the independent whole-branch reviews through R15, with all ten new production modules read in full, four new fixtures, all-six audit consumers and frozen acceptances, final verifier/packager/guards, independent dense checker, plan, provenance and current scope claims examined. No subagents, implementation, Lean/build/checker execution, repository/index/HEAD/cache mutation or evidence rewriting were performed. Only this report was written.

## Final-source mathematical review

- `NSP14/Homological/GradedCyclicPresentation.lean:15` defines the literal polynomial action on a chosen cyclic vector. The monomial-degree lemma at :20 and homogeneous-component/projection equality at :34 use the actual grading and actual polynomial action. At :53, applying this to the unit in degree zero proves that the actual algebra-map kernel is homogeneous. It does not assume the kernel is graded or equate Hilbert data with a nonmonomial quotient's Betti numbers.
- The surjective algebra map gives the actual quotient-module isomorphism at :75. At :87–107, the actual standard-monomial basis is transported through the quotient algebra equivalence, and each image has its actual grading degree. The degree-piece dimension theorem at :109 follows from this homogeneous basis. Its explicit finite-dimensional coefficient-algebra premise is appropriate for QC and is not imposed on the general non-Artinian BHP theorem.
- `NSP14/Homological/RelabelRegularGrading.lean:16` composes the original polynomial action with the genuine variable rename equivalence. The transported grading uses the same pieces, actual coefficient equivalences and actual variable maps (:20–45). Unit degree is preserved at :47, augmentation is preserved at :57, and :64 invokes actual totalBetti invariance under that augmentation-compatible polynomial equivalence. A bijection of labels is not mistaken for an unsupported graded or homological equivalence.
- `NSP14/Width/CoreLexPresentation.lean:16` chooses a genuine bijection Fin(q)≃D.a. The original internalToQCore action and actual QC grading determine the relabeled map and grading. Actual surjectivity and the actual QC unit-degree theorem discharge the cyclic-presentation hypotheses (:25–31). The kernel at :33 is a literal RingHom.ker. Its homogeneous quotient has exactly the original coreHilbert in every degree (:39), and actual total Betti numbers equal those of the original QC module (:44), via the real quotient-module isomorphism and relabeling.
- `CoreLexPresentation.lean:53` constructs one actual lex ideal over the original coefficient field, with the entire actual QC Hilbert function and the actual positive-row QC-to-lex total comparison. This connects the general BHP machinery to the same QC used by the width proof. Neither the lex ideal nor the desired Tor comparison is supplied as an extra premise.
- `NSP14/Lex/CorrectionHarmonic.lean:13` derives finite-dimensionality from an actual whole-tail Hilbert cutoff by injecting all standard exponents into finitely many finite degree sets. At :34, h_1=q proves absence of linear relations through actual monomial membership and degree cardinality. These are proved inputs to the existing actual cyclic harmonic theorem, not abstract dimension certificates.
- At :54, actual cyclic generation, actual degree-zero dimension and actual row-zero Betti value yield the first-row harmonic bound for this same lex quotient. The actual first-Betti identity C(q+1,2)+K then cancels the exact degree-one base contribution, giving K≤Σ (q−1)h_(d+2)/(d+3). All fractions, including 1/2 and 1/3, live in ℚ. The coefficient field remains arbitrary, including characteristics 2 and 3. At :98, replacing the positive denominators d+3 by 3 gives the stated third bound with a correctly directed inequality.
- `NSP14/Lex/TailHarmonic.lean:12` applies that estimate to the actual suffix comap quotient from R15. It proves properness, homogeneity, the high-degree Hilbert cutoff and absence of linear relations for that quotient; its degree-zero/one dimensions are established, not assumed to be equal to those of the larger ring. The high-degree Hilbert equivalence and exact sameCorrection equality transport the entire weighted sum and the same K back to the original lex ideal (:31–54). Thus the factor is r−1, while the original source's correction is retained. The theorem requires 2≤r≤q and the actual quadratic-cardinality threshold. The exact count of quadratic monomials is proved at :78.
- `NSP14/Lex/PrefixGeneratorCorrection.lean:12` defines S_j(n) by actual standard degree-n exponents supported in the first j variables. The double-counting identity at :15 counts each exponent exactly q−maxVariable times, and :35 identifies the paper's entire finite double sum with the same lexCorrection. The largest-variable minimal-generator count at :42 is actual divisibility minimality, not an independent sequence.
- At :55, actual strongly stable graded EK in the top row identifies that count. Positive q and nonzero minimal generators guard the q−1 and maxVariable−1 binomials. At :85 the actual top-variable standard partition is proved in positive degree. The recurrence at :108 is additive: g_q(d+1)+H_q(d+1)=H_q(d)+S_(q−1)(d+1). It holds for every number q≥1 of prefix variables and can be applied to the actual prefix comap ideals; it does not identify unrelated count sequences. The proof uses actual EK and the actual standard partition, while the earlier weighted generator identity supplies the finite telescope used in the Betti bound. The correspondence document records this alternative additive route.
- `NSP14/Width/DenseLexResources.lean:15` separates the actual core Hilbert sum into degrees zero/one and the high tail, giving tail+q+1=P_C. At :23, dense P_C≤q+1+2t bounds that actual high tail by 2t; the actual quadratic Hilbert value is at most that tail. The resulting one-lex-ideal suffix harmonic bound therefore applies with N=u−2 and the actual core cutoff. It yields the rational bound K≤2t(r−1)/3 for the same K.
- At :60 a single K and a single actual lex ideal work for every positive Betti row. For t=2, r=3 plus integrality gives K≤2; for t=3 it gives K≤4; for t≥4, r=t is legal because t≤q and the quadratic cardinality inequality is proved. Then 3K≤2t(t−1). The closure range is explicitly q≥4; the prior dense resource theorem retains its wider q≥3 range and t=0/1 cases. No q=3 dense closure is inferred.
- `NSP14/Width/DensePayment.lean:11` and :22 prove the first two binomial-increment terms by Pascal induction. The general payment at :54 is quantified over q≥4, 2≤t≤q and j≤q+1, with j=i−1 a genuine nonnegative index. It keeps the actual P, R and K premises rather than assuming the desired source comparison. The t=2 branch uses the exact adjacent-binomial identity and R=0; the t=3 branch uses K≤4 and R≤3; the t≥4 branch uses the proved nonnegative coefficient inequality. All rows through i=q+2, including the top, are retained. No division by a binomial that may vanish occurs.
- `NSP14/Width/DenseComparison.lean:16` combines the actual QC lex bound with `FullTransfer.actual_core_endpoint_bound`, including its kernel compensation and the original actualR term. The full source is the same actual D.fullG. It proves the first-term bound in rows 1≤i≤q+2 by the payment theorem and uses actual source vanishing above q+2. It never asserts target vanishing at the source's top.
- At :40, the actual completed tangent algebra of the original numerical semigroup S is recovered through completed_totalBetti, endpointData_totalBetti and fullG_totalBetti. At :50, row zero is handled as 1=1. In positive rows, u≤S.width is proved from physical width factorization V=d*u and d≥1, then the actual literal interval completion lower bound supplies the target. Source and target retain their own actual minimal variable sets. There is no d=1, gcd(m,u)=1, Cohen–Macaulay or P_C=P_G premise.
- `NSP14/Width/Closure.lean:16` covers every original physical narrow source with embedding dimension at least five. It first dispatches e=5 to the existing complete five-generator theorem. For e≥6 it uses q=e−2 and u≥q+1, handles u=q+1 and q+2, then sparse u≥2e−2. The remaining range has t=u−(q+1) satisfying 2≤t≤q and is passed to the new dense comparison. There is no uncovered boundary and no assumption that normalized width equals physical width.
- `audit/run18/DenseClosedGoals.lean:7` proves the exact frozen W_DENSE resource-and-closure conjunction. `audit/run18/ClosedGoals.lean:11` proves exact W_CLOSE, and :16 assembles all six original contracts. The acceptance files directly consume these declarations with the unchanged RequestedGoals types.

## Whole-branch contract and plan assessment

The previous reviews through R15 remain part of this continuation; their formerly open obligations are now resolved by named production proofs, not relabeled as complete. General arbitrary-characteristic BHP is obtained through actual initial-ideal comparison, actual coefficient extension and graded distraction preservation, a finite actual Hilbert-profile tower stabilizing at a strongly stable support, then the actual restriction/weighted comparison. It does not reuse characteristic-zero generic-initial strong stability in positive characteristic or assume rank equality across different characteristics. The exact frozen BHP is positive-row/all-Int; the EK formula has the correct quotient shift and actual finite minimal generators. General whole-Hilbert lex existence, ideal compatibility and finite generation were proved before this dense application.

The existing W_EDGE proof uses actual signed-unit Koszul minors, with diagonal ±1 and proved off-diagonal/cross-block zeros; characteristic 2 keeps the units nonzero. It retains the endpoint correction terms and d=1 AP source=target branch. The existing sparse proof connects distance-polynomial and all-higher-row estimates to the compensated actual source and physical target, including small embedding dimensions and the top row. The five-generator proof covers small widths and both nonantipodal/antipodal cases, uses the same actual QC presentation in the antipodal case, and keeps the u=7 improvement conditional on actual R>0. These earlier theorem types and proof sources are unchanged by this final production delta.

The original review focus is met: arbitrary fields; one actual whole-Hilbert lex ideal; integer/rational counting separate from k; the same actual compensated source; physical V=d*u and literal completion; q=3 resources separated from q≥4 dense closure; all boundary rows retained. The six closed IDs are W_SPARSE, W_FIVE, W_EDGE, X_BHP_EK, W_DENSE and W_CLOSE. The new proofs leave no mathematical Run18 obligation open.

The fixed plan permits alternative sufficient actual proofs when correspondence is documented. The current correspondence explains the strongly-stable/KK route to lex comparison, additive actual weighted-generator telescope, and actual suffix first-harmonic route to the same K. It does not claim an unproved terminal lex classification or literal reproduction of every source-paper proof. User-provided paper receipts state URLs, hashes, lengths and exact read scope; the PDFs are mathematical sources, not axioms or operational instructions. Acquisition is no longer blocked. The fixed mathlib provenance and Kneser source/license records remain available; historical partial reviews and failed attempts remain labeled as historical.

## Fixtures, independent arithmetic and attempt history

All four final fixtures were read. DensePayment names the q=4,t=2/3/4 boundary payments for every permitted j. WidthDense applies the actual fullG first-term theorem in every positive row over ℚ, F₂ and F₃. PrefixGeneratorCorrection checks the actual largest-variable minimal-generator counts of the mixed-degree ideal over those three fields.

`tests/WidthActualClosure.lean:12` consumes all six frozen contracts. Its SourceRow uses the literal original source and literal intervalCompletion with independent actual minimal variable types. BoundaryRows at :20 includes row 0, source e, source e+1 and the target's own actual embedding-dimension row. The original-source consumer at :24 uses physical D.d*D.u≤D.m−2. Fourteen actual models across ℚ/F₂/F₃ cover edge, dense and sparse boundaries, d=1/3, physical minimum m=d*u+2 and five-generator widths. The non-Cohen–Macaulay source at :234 retains the inherited actual PC=15, PG=10, R=1 data while applying the original-source comparison. These named applications test real theorem consumers, not detached numerical profiles.

The independent dense checker was read, not rerun by the reviewer. It separately enumerates 176,946 payments over q=4..80 and the full positive range through q+2. It builds actual core bases and per-characteristic matrices for six physical-minimum dense models, constructs the lex degree sets from their whole Hilbert functions, checks ideal closure and actual minimal generators, computes K and lex EK rows, and checks QC≤lex and the compensated payment. Characteristics 0/2/3 are computed separately. Its output explicitly identifies these as finite regressions, not a universal proof. Lean supplies universality.

The missing-import dense build01 and the focused29 parser failure/defProp warnings remain preserved and are not counted as successful verification. The six redundant warning-producing aliases were removed; actual consumer fixtures remain. Builds02/03 and root30 succeed, with root30 recording 6,652 jobs. Focused30, focused32 and focused33 have 8/2/9 individual exit-0 warning-free commands; their raw logs agree. Axioms27–29 cover the final actual QC, harmonic, dense, global and prefix exports. RED29/30/31 contain 9/2/1 intended named-missing-declaration controls, distinct from parser/import failures.

## Completed R16 independent evidence reconciliation

The execution agent reported the exact verifier process exit 0, and the completed verification.json and MANIFEST exist. I independently read and reconciled their contents rather than inferring success from that notification. R16 reports `PASS_RUN18_COMPLETE_VALIDATION`, `run18_complete: true`, 280 commands, 268 fixtures, 10,662 environment declarations and 2,421 new declarations. Every check passed, every command has its raw log, every command exits 0 without warnings, no expected-missing-declaration condition remains, and no failure.json exists. All current frozen acceptance files and the new DenseClosedGoals/ClosedGoals consumers individually execute successfully. closed_ids is exactly `[W_SPARSE,W_FIVE,W_EDGE,X_BHP_EK,W_DENSE,W_CLOSE]`; unproved_ids and expected_open_acceptances are both empty.

All 2,033 source SHA256 entries were independently recomputed and matched to exact Git blobs at `a5f480c5136042597fceae23ad06d2ef3923ed02`. Every current NSP14/test/audit Lean file is in this bound manifest. All 297 evidence hashes match; the evidence-manifest key set equals exactly the files in the R16 directory except the manifest itself. The proof snapshot and dependency snapshot agree with the frozen HEAD. The prior published R15 evidence commit is an ancestor. Source and bound evidence were not changed during this review.

All 7,212 retained verification/artifact files match committed Git blobs. All 6,838 such files present at the R15 proof source are unchanged in current HEAD and local bytes. Every R05–R15 final manifest entry was independently rehashed: respectively 198/204/222/234/240/253/261/267/274/280/289 entries, all matching. All 3,857 original baseline files remain unchanged except NSP14.lean, LEAN_PROGRESS.md and docs/LEAN_PAPER_ALIGNMENT_JA.md, whose authorized original byte prefixes remain intact. Frozen RequestedGoals and the plan are unchanged. RequestedGoals SHA256 remains `86a0a18eff0632cb915d67748dcef47a88991cebf287ef95750f58b450bea689`. The original physical target and six contract types were not weakened.

All 10,662 raw environment records were reconciled exhaustively with the processed records for name, defining module, exported kind, transitive axiom list, ordinary type and explicit type fields where emitted. Every recorded source SHA matches current source bytes. All 2,421 new declarations have nonempty ordinary and explicit type records, and every listed new source has declaration coverage. The normal and explicit final public types retain arbitrary Field k, the original S and physical-width premise, all i:Nat, literal intervalCompletion, and each ring's independent AtomExponent variables. dense_closed and width_closed have exactly Requested.W_DENSE and Requested.W_CLOSE; all_closed is exactly the conjunction of the six frozen IDs. No extra Tor inequality, Cohen–Macaulay, equality-of-P, normalization-d=1 or characteristic premise appears.

Every audited declaration's transitive axiom set is a subset of propext, Classical.choice and Quot.sound, with no self-axiom dependency. All added sources and the root contain no sorry/admit/sorryAx/native_decide or added mathematical axiom declarations. The genuine extra-axiom negative control is rejected, the proved exported-interface stub is accepted, and production has no dependency on the negative control. Thus an exported axiom-kind interface entry is not confused with a new unproved axiom; the dependency closure is actually checked.

Fresh-cache records cover all 141 production modules added since the original baseline, including all ten final modules, plus the project test and Run18 audit caches. Outside Lex/Width, the new Homological/Endpoint artifacts are explicitly retired as well. Snapshot records Lean 4.36.0-rc2, commit b35cb10cf2ced51a2fd1880cfdbf75c71ab7a35a, mathlib commit 139105d28c7685a154cb3093f79edb2e16708099, one fixture thread and 12,288 MiB memory limit. The current mathlib Git commit agrees with the snapshot. This is fresh project/new-production execution, not a claim to have rebuilt all external mathlib dependencies. The reviewer did not run a second Lean build or numerical checker.

The fresh dense output exactly matches the previously recorded focused output: 176,946 payments and six actual QC/lex models, each with separate characteristic-0/2/3 matrix results. All five independent Run18 models and inherited schedule/coordinate/additive regressions pass. The 23 publication guard cases pass. These bounded computations supplement, rather than establish, the universal Lean statements.

Two evidence-scope details remain explicit. First, the unchanged five-checker generator includes the legacy sentence “Run18 remains PARTIAL” in its supplemental finite-result note; it is not the authoritative scope declaration for the R16 run. R16's summary, exact six acceptance proofs and final review supersede that old checkpoint wording. Bound logs are preserved rather than retrospectively rewritten. Second, the ZIP source selection contains the Run18 scripts but not every inherited script they import or invoke. Those inherited bytes were verified against the retained original baseline and exact Git source snapshot. Reproduction of the full verifier uses that Git checkout; the ZIP must not be described as a standalone full-repository checkout. Neither detail changes the verified all-six mathematical result.

Final evidence SHA256 values:

- verification.json: `99b1c1d68b87d1e39bb94bfe93aa4a0d7ccd6fac8097f588c5a3722ac600c557`.
- SOURCE_SHA256.json: `5b9b0ca17bcb02600b6028d1b184cb671524743c79226e3f69a1c98e6b421537`.
- MANIFEST_SHA256.json: `1c5decbddcb9100223dfd9332dcdcf2d757b8240f7a6635b2abb2f3543b8d0d6`.
- declarations.json.gz: `f323dd993b72ca96db9760535fcf7b4b35b921f2d935da65fe7ceb44c0f3ea3c`.
- environment_axioms.log.gz: `40e9831ebae74a7c0d4ed0da351d2757863c42b13eead9f56722bba1fe9ab257`.

At finalization, HEAD remains the reviewed source. The R16 directory is untracked and is the only working-tree status entry. Its content and frozen-source binding are verified; no future evidence-commit binding is asserted by this source review.

## Publication scope and handoff

The complete verifier requires all six closure declarations and all frozen acceptances to succeed, no expected-open acceptance, all-six closed_ids, unproved_ids=[], and run18_complete=true. The packager retains exact source/evidence/review hashes and Git-byte checks, fresh-validation requirements, and safe immutable output paths. Its complete path additionally requires Critical/Important/Minor all zero, matching all-six review scope and empty pending/declined arrays. Complete versus partial archive labels are checked, and final status documentation must agree with the verified scope. Synthetic publication guard cases are controls, not mathematical evidence.

One publication detail was identified and resolved by the execution plan without changing frozen source: checked_payload validates the referenced review report but the packager includes only the fixed final-review document among its extra documents. The execution agent confirmed that decision.review_report will point to `docs/RUN18_FINAL_REVIEW_JA.md`, which will contain the complete report and will be included and hash-checked in the ZIP. Any optional separate raw report is not the decision's report target. The final ZIP must be inspected for that exact entry/hash.

At this source-review boundary, final evidence/document commit, publication-decision binding, COMPLETE ZIP entry/hash/CRC inspection, normal Push, remote SHA and final clean status are subsequent release operations. Their success must be observed separately, not presumed from a source review. The review covers mathematical all-six closure and the completed verification evidence; it does not falsely certify future publication operations.

## Final assessment

**PASS. Critical 0 / Important 0 / Minor 0. Pending `[]`; declined `[]`.** All six original frozen mathematical obligations are proved and pass completed R16 validation. General BHP/EK, whole-Hilbert lex existence, actual compensated dense comparison and global original-source physical-width closure are no longer open. No Run18 mathematical blocker remains.

This verdict certifies the exact proof source and evidence listed above. The remaining execution work is release binding: commit the immutable evidence and final status/review documents, verify that publication commit, create and inspect the COMPLETE audit ZIP with its referenced report included, and perform/observe the authorized normal Push and final remote/clean checks. These future actions are not already certified. No later or /tmp-only prototypes are included in the proof or evidence scope.


## 以下は旧checkpointの履歴（現在の未完事項ではない）

# Run18 PARTIAL：最終レビュー・検証結果

> 最新結果は末尾の「2026-11-14 継続checkpoint」を参照。直下は11月13日の公開記録。

## 2026-11-13 checkpoint

**Run18全体は未完。閉鎖はW_SPARSEのみ。PARTIAL checkpointとして公開可。**

- baseline: `c4fd8153f55bb231aab4168a47c1546888fa7ab0`
- 指令: `131f559a9ad495891f0aab487f969bf91b5a447f`
- proof/source snapshot: `fa3787cff6e924690ea7abc1bc522fb43a06be02`
- review/evidence head: `008b3247442e6ab5d6f2e1cf025855d629bfc542`
- [最終検証R03](../verification/run18/runs/release_candidate_20261113_r03/verification.json)：172 command、159 fixture、未完5契約の指定宣言不在確認、8429宣言・新規188宣言の型/公理依存。既存証跡3165件を保持。
- 新規production：13 module、868行。`NSP14.Run18.sparse_closed`が凍結された`Requested.W_SPARSE`を証明。
- 未完：`X_BHP_EK`、`W_EDGE`、`W_DENSE`、`W_FIVE`、`W_CLOSE`。一般BHP/Pardue・EKのLean証明を構成できておらず、全Run18/全域P14を完成認定しない。

本番証明の推移公理依存は`propext`・`Classical.choice`・`Quot.sound`のみ。verification内の追加axiomは隔離された拒否用negative controlで、本番・fixture・本環境監査からimportしていない。

## 別コンテキストのwhole-branchコードレビュー

read-only reviewer `/root/run18_final_review` による結果。checkout・index・HEAD・cache・証跡を変更せず、検証scriptも再実行していない。これは今回の差分の最終コードレビューであり、既存全数学や未完Run18の独立完成監査ではない。

**Critical 0 / Important 0 / Minor 0。PARTIAL公開を妨げる実欠陥は検出なし。**

確認内容：

- 新規production 13 moduleを通読し、V03 V.3／V02 §13.4と照合。`sparse_closed`は元の`Requested.W_SPARSE`を追加比較前提なしで証明する。
- `SparseComparison`は同じS・体kから、双方自身の最小変数列を持つ完備接錐のactual Bettiを比較する。targetはliteral interval completionで、正規化幅uは`u≤S.width`を介して物理幅へ戻す。
- `FirstResources`／`SparseHigher`はactual QCと補償済みtransferを使用。`P_C=P_G`、`R=0`、標数間rank一致を仮定せず、有理重みの除法はℚ上。
- `NormalizedCapacity`は正の二項係数分母を確認し、`i=e`を基点で別処理。`e-i`で上端を割らず、`i=0/1`、`2≤i≤e`、`i>e`も最終比較で分離。Nat減算も加法形・範囲証明を伴う。
- Lexの成果は定義、一般斉次商の次数piece有限性、actual graded/total Torの接続に限定。非Artin商を排除せず、`finrank`の無限次元時の値に依存しない。
- 43の具体fixtureと計算cacheを確認。cacheは全次数のactual offset sumsとの等式から各計算対象との等式を導く。一般証明へ有限表を代入していない。
- R03の172 command、159 fixture、5件の指定宣言不在、guard・数値・公理対照結果を既存出力で確認。8429宣言の依存は許容3公理のみで、negative-control axiomは本監査にない。
- SOURCE manifest 1093 entryは現在のbytes・source commit・review commitと一致。evidence manifest 185 entryはcoverage、現在のbytes、review commitと一致。baseline全ファイルも、指定3ファイルの追記を除き不変。
- `collectAxioms`によるexported theorem stub分類と、本物の追加axiomの自己依存拒否は整合。R01/R02は失敗のまま保存。
- packagerはPARTIAL範囲、cold検証、review判定・hash、source/evidenceのgit bytes、追加payload、既存出力拒否、ZIP内容hash/CRCを検査する。

台帳の判断について、inline記録、独立な疎幅実装、e≥7の第二行多項式統合、PARTIAL表示は今回の結果と整合する。後続の直列elaboration、証明付きcache、stub分類修正も、受入命題や数学的依存を弱めていない。

**Safe to publish as PARTIAL? Yes.** review対象を既存packagerのgateを通したPARTIAL checkpointとして公開してよい。

**Full Run18 complete? No.** 閉鎖はW_SPARSEのみで、元のFULL Run18依頼は完了していない。

## Reviewerが判断を保留した事項と実行側の判断

1. **未実装5 IDの数学的完成度。** 公開証明がなくacceptanceも失敗するため完成認定を保留。実行側もopenを維持し、PARTIALとして公開する。誤って完成扱いすれば未証明公刊入力・全幅合成を隠すため、status/ZIP/gateで一IDのみと固定する。
2. **未取得の公刊本文の証明再構成。** 書誌情報だけで任意標数の証明を認定しない。実行側も未取得・未構成として保存する。誤れば引用をLean証明の代わりにするため、X_BHP_EKの受入失敗を残す。
3. **既存baseline全数学の独立再証明。** 新規利用箇所の型・接続と回帰を確認したが全定理を再導出していない。実行側は既存sourceのbyte保持・回帰・公理抽出を根拠に再利用し、全baselineの独立再監査とは表示しない。既存の意味上の誤りがあれば波及し得るという限界を保持する。
4. **新規実行による性能・OOM原因確定。** reviewerはread-onlyで再実行していない。実行側も累積OOM counterを当該processだけの回数と断定せず、SIGKILL/再帰深さ失敗と修正版の実測成功を区別する。誤った原因断定は再現性の判断を損なうため、失敗記録を保持する。
5. **実際のZIP作成・公開・remote Push。** review時点では未実行。実行側がreview済みsnapshotに対するpackager、全entry/hash/CRC、通常Push、remote SHA・clean確認を別途行い、公開receiptへ記録する。未実行の公開成功をレビュー結果として先取りしない。
6. **有限fixtureの網羅性による全称性認定。** 有限検算は補助証拠に限定し、全称性はLeanのW_SPARSE閉鎖から判断する。有限範囲を一般証明へ代用する危険を避ける。

実装時の判断とその限界の全記録は[実行台帳](RUN18_EXECUTION_LEDGER_JA.md)、原稿対応と残る正確な義務は[原稿対応](RUN18_PAPER_CORRESPONDENCE_JA.md)を参照。

## 2026-11-14 継続checkpoint

**PARTIALとして公開可能。Run18全体は未完、完全閉鎖は引き続きW_SPARSEのみ。**

- proof/source: `f1732ce45500a191df2b76780f5feddd3d87adfa`
- evidence/status/ledger: `81bdbe66055d7ade9ef0d9e2f9ef00745bb3ea7d`
- reviewed head: `decdb7142cb5272c13a75a7536a8b4d3fbef6fdc`（直前commitとの差は検証完了とreview gateを分けるstatus文字列一行のみで、reviewerも追加確認）
- [R04検証](../verification/run18/runs/release_candidate_20261114_r04/verification.json): **179 command／165 fixture、8594宣言／新規353宣言**。公理依存は許容三公理のみ。1139 source entry、193 evidence entry、開始時3388証跡のbyte保持。
- 追加production: 7 module、774行。新fixtureの名前付き定理53件。凍結した六契約と既存疎幅証明は維持。

既存read-only reviewer `/root/run18_final_review` が継続差分 `aa29347..f1732ce` とwhole branchの接続・R04証跡を追加確認した。新たなfresh-context reviewerを起動したという表示はしない。ファイル・cache・HEADへの変更、並走buildは行っていない。

**Critical 0 / Important 0 / Minor 0。Safe as another PARTIAL checkpoint: Yes。Full Run18 complete: No。**

確認した追加経路：

- denseのprefixは同じ実CoreMinimalから端点factorを排除し、元の向きの欠落剰余へ単射を構成。元のW/P/R/Hxへ接続し、`dense_resources_closed`が元のRequested.DenseResourcesそのものを証明する。DenseClosure／W_DENSE全体の閉鎖とは区別。
- AP edgeは実offsetから実AP sourceを識別し、d=1はliteral targetとのcarrier equality、d≥2は物理幅で支払う。双方自身の最小変数列、任意体、全iを保持。
- 五生成元小幅のR>0改善は元のactualR→元のHx→実QC高次基底であり、Rhatへのすり替えなし。第二行44/68という十分な別上界とtarget46/77の接続は台帳どおり。
- u≥8の高次行は全構造を扱い、非antipodal第一行は同じDのresidueAlphabetへ仮定を掛ける。二項係数の取消し・Nat減算・上端・source消滅後の範囲を確認。有理重みを係数体内で割らず、有限検算を全称証明へ代用しない。
- 全source/evidenceは現状・proof/evidence git bytesと一致。coverageも完全。前回公開時のverification/artifacts3355ファイルは独立照合でも不変。12,852算術check／35 actual core例にはu=7の元のR>0例（PC10、PG7、R1、Hx3）と、標数0/2/3の個別matrix計算が含まれる。

reviewerが判断を保留した事項と実行側の判断：

1. **未完五ID**：一般BHP/Pardue/EK、一欠落rank、dense lex比較、antipodal第一行／実presentation、全域合成はopenのまま。誤って完成扱いすると未証明の全域定理を公開するため、五つの失敗受入とPARTIAL gateを保持する。
2. **原稿の強い中間式との同一性**：今回の十分な別評価として採用。強い40/62やantipodal presentationを証明済みとはしない。誤れば紙との対応が誤解されるため、差分を原稿対応と実行台帳へ明記した。
3. **有限検算による全称性**：一般性はLean定理から判断。checkerは補助に限定。誤れば有限例を一般証明に代用するため、statusにも有限検算であることを残す。
4. **baseline全数学の独立再証明**：利用する型・接続・差分・回帰の確認までとし、全既存定理の再導出を認定しない。既存の意味上の問題が波及する可能性は残る。
5. **実ZIPとremote公開**：review時点の未実行操作は認定しない。実行側が既存gate、全entry/hash/CRC、通常Push、remote SHAを確認し、新しいreceiptへ保存する。未実行成功の先取りを避ける。
6. **別名review report対応**：今回も既存固定reportへ追記するので、別名reportをpayloadへ自動追加しないpackagerの一般化は不要。誤ればreport欠落となるため、今回のZIPにもこのreport本体を含むことを検査する。

軽微な指摘の繰越はなし。未完の計画workspaceは継続用に保持する。追加の正確なexport・paper variant・残る義務は[原稿対応](RUN18_PAPER_CORRESPONDENCE_JA.md)と[実行台帳](RUN18_EXECUTION_LEDGER_JA.md)を参照。


## 2026-11-14 五生成元全域閉鎖・R05 最終レビュー

# Run18 five-generator closure: final whole-branch review

**Verdict: PASS for publication as an honest PARTIAL checkpoint. Critical 0 / Important 0 / Minor 0. Full Run18 complete: NO.**

This completes the same review whose static phase is recorded in `/tmp/run18-five-review.md`; it is not a second independent review. Source snapshot: `bc554ffc0231c0e83fdf4c62673e438cc123c417`. Reviewed evidence/status/ledger commit: `b22600b61e013da0e3d55e5a6b0559216cc4d76f`. Whole Run18 range starts at `c4fd8153f55bb231aab4168a47c1546888fa7ab0`; continuation focus starts at `e4bb337900e75bdb15e609b2518e8a02009565ca`. The evidence commit changes no source-bound bytes from the static review.

## Mathematical and contract findings

No actionable defect was found. The following are checked properties, not unresolved findings:

- `audit/run18/FiveClosedGoals.lean:7` proves the exact frozen `Requested.W_FIVE`. `RequestedGoals.lean` retains SHA256 `86a0a18eff0632cb915d67748dcef47a88991cebf287ef95750f58b450bea689`.
- `NSP14/Width/FiveComparison.lean:13` compares actual total Betti numbers over each ring’s own minimal variables, for the original S, arbitrary field k, physical narrow-width hypothesis, every row i, and the literal interval completion. Its lower-width proof and 4/5/6–7/at-least-8 split cover every allowed width. No comparison-valued hypothesis was added.
- `NSP14/Width/AntipodalPresentation.lean:139` derives the actual coefficientwise kernel from the surviving basis and injectivity of surviving exponents. `AntipodalIdeal.lean:102` identifies the literal ideal `(YZ,Z²,ZW)+(Y,W)^h`. Lines 110, 117, 140, 154 and 164 retain the original quotient map, variables, polynomial-module action, actual Tor and degrees. The hypothesis is gcd(t,h)=1, not gcd(t,2h)=1. `AntipodalBasis` and `AntipodalVolume` establish actual P=C(h+1,2)+1 and W=h²−h+2.
- `AntipodalComparison.lean:76` pays the first row with the proved P bound and rational harmonic inequality. It does not import the unproved universal equality b1=h+4. The documented alternative proof is sufficient for the frozen comparison.
- `FiveHoleKernel.lean:145` proves the actual internal-omission kernel has five explicit generators. `FiveHoleTopRank.lean:43` constructs a signed unit minor in the actual top Koszul differential. Its diagonal ±1 entries remain units in characteristic 2. `FiveHoleComparison.lean:30` uses actual Euler, this rank bound and original P bounds; edge omissions use P≤5. The final comparison returns to the same S and physical-width target.
- SparseComparison, FirstResources, NormalizedCapacity and SparseHigher preserve actual QC-to-G transfer, original resource quantities, rational weights, positive denominators and endpoint cases. No field-characteristic division, P_C=P_G assumption, reflected-source replacement or cross-characteristic rank equality was introduced. The top row is not divided by e−i; zero and source-vanishing rows are handled.
- Dense resources include q=3 and are correctly distinguished from the still-open q≥4 DenseClosure. AP edge identifies the actual carrier and retains d=1 source=target and d≥2 physical-width payment. The u=7 improvement is conditional on original R>0. Neither partial result is advertised as full W_EDGE/W_DENSE.
- Lex definitions and degree-piece finiteness remain preparatory results. The general arbitrary-characteristic BHP/Pardue/EK theorem and one whole-Hilbert-function lex comparison remain explicitly open. No unsupported characteristic-zero argument or comparison tower substitutes for them.
- Tests exercise original-source all-row consumers, widths 4/5/6/7/8/9, physical boundary m=du+2 with d=3, nonunit t=2,u=10 and fields of characteristic 0/2/3. Independent finite rank checks are explicitly labeled finite evidence. Universal closure is supplied by the Lean contract, not by enumeration.

## Completed R05 evidence inspection

The reviewer did not rerun Lean/lake or alter cache/repository files. Existing R05 output was inspected, and independent read-only hash/git comparisons were performed.

- R05 records **183 passing expected outcomes, 169 fixtures, 8942 environment declarations and 701 new declarations**, in 695.647 seconds of recorded command time. The fresh-cache record names the removed test, Lex/Width lib/IR and Run18 audit caches; the source snapshot fixes Lean 4.36.0-rc2 and mathlib `139105d28c7685a154cb3093f79edb2e16708099`. The build log ends successfully with 6040 jobs.
- `FiveClosedGoals` and the original W_FIVE acceptance both exit 0. The four open acceptances each contain only the expected unknown-identifier diagnostic for bhp_ek, edge_closed, dense_closed or width_closed. Those declarations are absent from the actual environment inventory.
- All **1226 source manifest entries** match current bytes, proof-commit bytes and reviewed-commit bytes. All **198 evidence entries** match current bytes and reviewed-commit bytes, with complete directory coverage. The manifest itself matches the reviewed commit.
- All **3653 verification/artifact files present before R05** were independently compared against source-commit bytes and remain identical. Failed R01/R02 evidence stays preserved as failed attempts. From the Run18 baseline, only the three designated append-only files change; their exact old prefixes remain intact.
- The raw collectAxioms output was compared with the processed declarations. Every actual transitive dependency is among `propext`, `Classical.choice`, `Quot.sound`; no declaration depends on itself. Normal and explicit types exist for all 701 new declarations. Main contract, original-source comparison, actual presentation/Tor and rank types were inspected.
- Recorded exported kinds are 1811 definitions, 6699 axiomInfo interfaces, 388 theorems, 14 inductives, 16 constructors and 14 recursors. The 6699 interfaces are valid exported proof stubs under the transitive-dependency test, not additional mathematical axioms. The isolated real-extra-axiom control is rejected by its self-dependency; that probe is absent from the production inventory.
- Publication controls report 15 passing guards. The finite five-generator checker reports nine actual cores and five presentation examples, with its non-universal status explicit. Old replay checks and all other recorded checks pass.

Evidence hashes:

- verification.json: `1d2f962be3ed96be2a0649c13d55396ce75dff6f1a9ae5858173e4e73570342f`
- MANIFEST_SHA256.json: `b7178751b483e05f27413a4b5a3622db375b3a231814b66c00e797ff1f30fefd`

## Publication scope and limitations

Current status and appended ledger agree: **W_SPARSE and W_FIVE closed; X_BHP_EK, W_EDGE, W_DENSE and W_CLOSE open**. The handoff preserves their exact frozen types, distinguishes q=3 width-5 ranks from general one-missing-offset ranks, records the alternative antipodal first-row proof, and does not promise completion in two further runs. Historical status sections are marked historical. These Rulings are consistent with the inspected code and evidence.

The reviewed packager binds source, evidence, review decision/report hashes and reviewed git bytes, requires the exact PARTIAL scope and cold successful checks, refuses an existing output, and checks archive contents/hash/CRC. The fixed `docs/RUN18_FINAL_REVIEW_JA.md` body is explicitly included in its payload. Publication is safe through those existing gates after this review is recorded. No mathematical or evidence fix is requested.

The reviewer declines to certify:

1. Completion of the four open IDs or full Run18/whole-domain NS-P14.
2. A universal exact antipodal b1=h+4 theorem, or stronger paper intermediate bounds replaced by sufficient proved alternatives.
3. Independent rederivation of every inherited baseline theorem or inaccessible published source text; the review checks relevant connections, unchanged bytes and recorded regression/dependency evidence.
4. Finite examples as proof of universality, or independently rerun build/performance/OOM behavior; this reviewer remained read-only.
5. Future review-decision file creation, ZIP creation/CRC/hash results, remote Push and final remote SHA/clean status. These actions have not yet occurred at this review boundary and must be observed separately by the execution agent.

The review’s positive PARTIAL verdict is not a claim that future publication actions have already succeeded. No repository/cache mutation, Lean/lake execution, commit or agent spawning was performed by this reviewer.

## 2026-11-15 R14：一般BHP/EK認証


R14 cold全回帰成功：証明source 22cbb0ed5b6a2f48b66d35b2aee34f9f488bef57、264 command/251 fixture、10334宣言・新規2093宣言、1882 source hash・280 evidence hash、6523既存証跡のbyte保持。全宣言の推移公理は許容三公理のみ、自己依存なし。五production module/新audit/凍結BHPEK acceptanceをcold再構築/検査。独立レビュアーは全raw/processed宣言、normal/explicit型、全source/Git blobs、manifest、旧6523/前6213/baselineとR05–R13 manifestを照合し、Critical/Important/Minorすべて0、pending/declinedなし。report verification/run18/general_bhp_review_20261115.md、decision review_snapshot_general_bhp_20261115.json。summary SHA256 bfac554d8da937049de88c0ae1bd55d2e1667ac969605ef67dc221f48b9d4a81。
一般任意標数の全positive行/全Int次数のactual BHPと凍結X_BHP_EKを認証。六IDはW_SPARSE/W_FIVE/W_EDGE/X_BHP_EKの4閉鎖、W_DENSE/W_CLOSE未完。一般whole-Hilbert lex存在・残るTask2 concrete acceptanceはこのsourceでは未完。後続/tmpのLexExistence/TotalBHP/LexCorrection等は認証対象外。Run18継続、Run19保留。

## 2026-11-15 R15：一般lex存在とK計数認証


R15 cold全回帰成功：証明source 6074994621ca5b57be28d44729a8ebab46f700a6、273 command/260 fixture、10461宣言・新規2220宣言、1931 source hash・289 evidence hash、6838既存証跡のbyte保持。全宣言の推移公理は許容三公理のみ、自己依存なし。八production module/九fixtureをcold再構築/検査。独立レビュアーは全raw/processed宣言、normal/explicit型、全source/Git blobs、manifest、旧6838/前6523/baselineとR05–R14 manifestを照合し、Critical/Important/Minorすべて0、pending/declinedなし。report verification/run18/lex_existence_correction_review_20261115.md、decision review_snapshot_lex_existence_correction_20261115.json。summary SHA256 fe8e7927f8251a05efff2c7dcf7533eee9156f89460e50a8790abef80e8b1186。
一般whole-Hilbert lex存在、actual total BHP、有限standard K identity/全行bound、actual suffixの高次Hilbert/K一致と三変数nonlex actual Q/F2/F3 acceptanceを認証。一般lex存在は以後の未完理由ではない。四ID閉鎖/二ID未完を維持。dense harmonic支払いとactual QCへの適用/global閉鎖はこのsourceでは未完。後続/tmpのgeneric cyclic kernel/presentation/relabel、actual core lex、K harmonic/dense resource、numeric paymentは認証対象外。Run18継続、Run19保留。
