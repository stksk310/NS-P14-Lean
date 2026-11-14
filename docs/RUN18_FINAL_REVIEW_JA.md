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
