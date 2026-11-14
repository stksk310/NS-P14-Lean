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
