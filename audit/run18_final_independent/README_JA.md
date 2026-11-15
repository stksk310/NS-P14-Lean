# Run18 最終独立監査 — COMPLETE 監査通過

対象は公開 work / run18/implementation-20261113 の **345e2d82fea50ef89e00a8f35c4fb53ac601d7ce**。2026-11-15 に隔離チェックアウトで実施した。**Critical 0 / Important 0 / Minor 0。Run18 の六目標すべてについて通過、修正要求なし。** この判定は NS-P14 全体の完成宣言ではない。

旧 PARTIAL 監査（58a0f546、監査記録47aeeb4359）を上書きせず、その後追加された証明・接続と COMPLETE 公開証跡を再監査した。数学ソース・凍結契約・既存証跡・既存ZIPは変更していない。本ブランチは新規監査報告と独立再検証ログだけを追加する。

## 1. 凍結した完成条件との対応

元指令は `docs/superpowers/plans/2026-11-13-run18-lex-width-closure-order.md`（131f559a）。`audit/run18/RequestedGoals.lean` は導入時cdce65adから不変で、SHA256は `86a0a18eff0632cb915d67748dcef47a88991cebf287ef95750f58b450bea689`。完成条件を緩めた置換はない。

| 契約 | 監査結果 |
| --- | --- |
| W_SPARSE | actual sparse dataから既存数値比較へ接続。以前の監査後も証明保存、回帰成功。 |
| W_FIVE | actual五生成元の分岐を原稿対応済みの十分な評価で閉じる。凍結契約を証明。 |
| W_EDGE | 実際のQC作用とKoszul微分上の符号付き単位minorから必要rank下界、actual Rと原子によるtargetまで接続。 |
| X_BHP_EK | 任意体・一般斉次idealの全次数lex存在とgraded BHP、実際のgraded homologyに対するEKを実証明で供給。 |
| W_DENSE | 一つのactual Lと一つの補正Kを全行で共有。actual core、資源、同じcut、actual R、元のSとliteral interval targetへ接続。 |
| W_CLOSE | e≥5の全幅範囲を分岐し、任意体・全Betti行についてactual比較を合成。 |

`NSP14.Run18.all_closed` が六つの元契約の連言を直接証明する。公開consumerは `NSP14.NumericalSemigroup.narrow_width_comparison`。元のSとliteral interval completionのそれぞれの最小表示変数を用いたactual completed tangent algebraのtotal Betti比較であり、補助データの存在を未証明仮定として要求しない。主要exportの通常表示・完全表示・依存公理は [selected_exports.json](selected_exports.json) に保存した。

## 2. 独立ソースレビュー

四つの読取専任レビューを分担し、最後に親監査で契約・consumer・証跡の接続を照合した。各報告の担当外という留保は、下表の隣接担当および親監査で補っている。

| 報告 | 読んだ主な証明経路と接続 |
| --- | --- |
| [BHP_REVIEW.md](BHP_REVIEW.md) | 実際のinitial idealと全次数HF、三角Koszul blockによるrankの方向、distraction ideal・次数別同型・符号・任意標数、同標数拡大と下降、generic進行と停止、strongly stable比較への接続。exterior/grading/scalar比較の支持モジュールも追加読了。 |
| [LEX_REVIEW.md](LEX_REVIEW.md) | 全次数で一つのlex ideal、無限支持を許す一般斉次商、有限HF profileの正当化、colex/degree separator、生成元分解、literal Kの望遠和、suffix quotientと同じKの調和評価、total化の有限支持。 |
| [EK_EDGE_REVIEW.md](EK_EDGE_REVIEW.md) | 実際のcolon/短完全列/Tor零写像、graded split・座標idealのhomology・正しい次数差、strongly stable EK一般化。one-hole actual作用・mate・単位minor・標数2・補正と端行・target接続。追加支持モジュールも読了。 |
| [DENSE_REVIEW.md](DENSE_REVIEW.md) | actual core presentationと全HF・Betti移送、同一L/Kと同一cut、q=3/≥4、rational支払いと端行、物理幅への移送、e=5/≥6と全幅分岐、元契約・原稿差分との整合。 |

親監査では最終Closure/DenseComparison/CoreLexPresentation、BHP/lex/totalのexport型、六契約の閉鎖定理、検証器・packager・公開決定・Gitとアーカイブの結合を照合した。ベースライン以後の新規productionは141モジュール15,485行。旧監査対象58a0f546以後は104モジュール11,766行の追加であり、既存productionの改変はない。

特に確認した点は、一般BHPにArtin性を仮定していないこと、lex idealを次数ごとに取り替えていないこと、体拡大と異標数の同一視を混同していないこと、chain全体の無限次元をfinrankで消していないこと、符号付きminorが標数2でも非零なこと、denseの各行で同じ補正Kを使うことである。

## 3. 新しい独立再検証

実行コマンド：

```sh
PATH=/tmp/ns-p14-lean/bin:$PATH python scripts/verify_run18.py \
  --fresh-test-cache \
  --output-dir verification/run18/runs/independent_final_audit_20261115_r01
```

Lean v4.36.0-rc2、mathlib 139105d28c7685a154cb3093f79edb2e16708099。依存キャッシュと監査済みベースラインのビルドキャッシュは再利用し、新規Run18 productionおよび全fixtureのキャッシュを除いて実行した。**全ベースラインを含む完全cold buildとは称しない。** 新規141 productionすべての実ビルドをbuild.logで確認した。

- 280コマンド、268 fixtureすべて成功。結果は `PASS_RUN18_COMPLETE_VALIDATION`。
- 六closed ID、未完IDなし、open acceptanceなし。標数2を含むactual回帰も成功。
- チェック実測時間の合計は1379.479秒（各コマンドの合計であり、レビュー所要時間ではない）。
- 環境10,662宣言、うち新規2,421宣言。新規分は通常型・完全型を保存。再実行と公開R16の全宣言・型・依存一覧が完全一致。
- collectAxiomsで許容されるのは `propext` / `Classical.choice` / `Quot.sound` のみ。自己公理依存なし。余分な公理の検出対照も成功。
- Leanの公開proof interfaceがaxiomInfoに見えることだけでは未証明とは判定しない。実際のcollectAxiomsと定義本体・元ソースを照合している。
- 既存の検証・artifact 7,516ファイルを保存。旧独立監査のファイルも元コミットとbyte一致。

全出力は [独立再検証ディレクトリ](../../verification/run18/runs/independent_final_audit_20261115_r01)、実行標準出力は [verification_stdout.log](verification_stdout.log)。[check_fresh_evidence.py](check_fresh_evidence.py) はmanifest・全宣言・型・新規実ビルド・旧監査保存を再照合し、結果を [fresh_crosscheck.json](fresh_crosscheck.json) に保存した。

## 4. Lean実装から独立した有限モデル

[check_graded_models.py](check_graded_models.py) はプロジェクトの数値実装をimportせず、斉次idealの実際の次数別商空間・変数作用・符号付きKoszul行列を有理数と有限体上のRREFで計算する。9例×標数0/2/3＝27例、内部次数0〜8で864比較セルを調べ、29セルで厳密な改善があった。lex側のEK式との一致も照合した。0変数・1変数・非Artin主ideal・非lex完全交叉・unit idealを含む。

`(x²,2xy,y²)` は標数2と3でHFが変わる対照であり、異標数のBetti保存は前提にしていない。各体自身のHFからlex側を作った。これは一般定理の代用ではなく、方向・次数・符号・端例への独立回帰である。全結果は [graded_models.json](graded_models.json)。

## 5. 公開COMPLETE証跡

[check_published_evidence.py](check_published_evidence.py) により、R16のsource manifest 2,033項目・evidence manifest 297項目をGitのproof snapshot a5f480c5、reviewed snapshot c97fa324、対象345e2d82と照合した。公開決定のreport本文とhash、六目標、指摘0、pending/declinedなし、公開receiptを確認した。proof snapshot時点の旧証跡7,212ファイルも保存されている。

既存Run18 ZIP四本すべてについてCRC・内部SHA256・重複entryを検査。最新 `artifacts/NS_P14_LEAN_RUN18_COMPLETE_20261115.zip` は2,338 entries、4,580,933 bytes、SHA256 `1acfe35915b20c4c870a148a6a39d833a1f796de4f62f3f83ba280ca894c774d`。payloadと現在のGit/source/evidence、同梱のreview全文・公開決定が一致した。既存ZIPへのpackager再実行がexit 2で拒否され、bytes不変であることも実確認した。詳細は [published_evidence.json](published_evidence.json)。

## 6. 原稿対応と引継ぎ

原稿より弱くても完成条件を満たす十分な評価を使った箇所は、元指令の許容範囲で、既存原稿台帳にも明記されている。

- antipodalの一般的な厳密等式 `b₁=h+4` はexportしていない。actual五生成元比較は別の上界と資源支払いで証明した。
- one-holeの全rank/Betti厳密等式ではなく、actual符号付きminorによる十分なrank下界を使う。
- 五生成元の小さい第二行は原稿の40/62に代えて44/68を使うが、target 46/77に収まる。

これらは元の六契約の弱体化や未完入力ではない。将来の論文では実際に形式化した十分な証明を採用する。Run18の論理的な未完は検出しなかった。次の担当は既定のRun19（N4・e≤3・LTV）とRun20（全体合成）である。

本監査は固定された既存ベースラインとmathlib全証明の独立再証明ではない。その依存と保存を明示し、新規証明経路・actual接続・全回帰・公理依存・公開結合を監査した。元workspaceは変更せず、本監査ブランチを後続スレの引継ぎ入口とする。
