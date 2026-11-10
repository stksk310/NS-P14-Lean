# Run12実行台帳

指令：docs/superpowers/plans/2026-11-10-run12-coordinate-closure-order.md。
Base：a6aac7b345e3e7dbd3ac660468bdd220ecfa7dca（Block11完成・26検証・443公理依存・42既存hash・Push済み）。
計画ブランチorigin/plan/p14-20-runs-20261110をfetchし、指令と全体計画・機械可読計画をそのまま取り込んだ。
既存work branchを継続。変更のない過去の検証原本を保持する。

## 完成条件（未完を完了へ読み替えない）

- [x] actual非x原子のS₀、G/T/A/N/Q作用とA/Qへの全射。
- [x] actualなD_sT・F_sNとS₀作用安定性（JumpFiltration；斉次性とstrata接続は次項）。
- [x] 同jump strataのactual S₀線型同型と実継承次数差s。
- [x] 全terminalで2≤jump≤ν、δ=0でactual T=N=0。
- [x] formal k[[S]]の実極大イデアルの接錐と既存Gの次数付きk代数同値・自然単項式対応。
- [x] 受入テスト・全新宣言の公理依存・旧回帰・台帳・監査引継ぎ・監査ZIPの公開準備。Push後のHEAD/remote/clean照合は末尾の公開手順。

## 実行順

まず最大表示のlive splitと直接jump上限を証明する。これはTask3を、Task1–2と独立な既存のactualνへ接続する短い証明候補。
次にS₀作用とfiltration/strataへ進む。完備化比較は、形式級数をsupport⊆SのPowerSeries部分環として直接定義する方針を調査する。
後者を採用すればm-adic completionと形式級数の同定を仮定する必要がなく、実極大イデアル冪の係数条件を証明する必要がある。

## 実装過程の到達記録（下記の最終接続で更新）

- LiveSplit / JumpBounds：最長表示の切断から全terminalの上限を直接証明。原稿のGröbner/生成次数経路を置換。
- PolynomialAction / PolynomialPresentation：同じactual非x原子のS₀がG/T/A/N/Qへ作用し、A/Qへ全射。
- TerminalCoordinates：terminal/headの型付き再添字、k線型同値、単項式次数差、δ=0のactual核/イデアル消滅。全体のS₀線型同値ではない。
- JumpFiltration：actual T/Nの支持条件がactual G/A乗算で安定、S₀部分加群と反対向きの包含を証明。strata同型はまだ未接続。
- FormalSemigroupRing / FormalOrder / FormalFactorization：support⊆SのPowerSeries部分環を直接採用。定数項kernelはField上で実極大イデアル。order=nの接頭部の有限集合に無限係数を分配し、実極大イデアル冪と係数条件の同値を証明。
- FormalTangentAlgebra / FormalTangentScalars：実冪の商の乗法・単位・k代数構造。
- FormalInclusion / CompletedPieces：自然なk[S]→k[[S]]と係数一致、order=n切詰め、各実冪の商の自然線型同値と積の一致。
- CompletedComparison：次数付きk代数同値を構成中。未完の同jump S₀加群同型を完了と読み替えない。

旧Block11までのソース・検証原本は未変更。追加ソース全体のaxiom監査・受入試験・最終外部レビューは本runの後半に実施する。

## 最終接続

- JumpSliceのkernel/surjectivityから、実S₀部分加群の次/前の商をexact-jump座標と同定。
- JumpActionで同jump両端のactual積の行列係数が一致することを証明し、Gの基底から任意のactual G元へ拡張。
- JumpStrataの`jumpStratumEquiv`でS₀線型性と両方向の逆を閉じた。
- JumpDegreesはG/Aから実斉次代表元を引き戻し、商へ送った次数部分を定義。同じ同型のp→p+sを任意の商元について証明。
- JumpHomogeneityで実成分射影に対する安定性とD₂=T、D_(ν+1)=0、F₁=0、F_ν=N。
- PolynomialGradingでG/T/A/N/Qそれぞれの変数による次数1の整合性を明示。
- CompletedComparisonの自然な次数付きk代数同値、CompletedTransportのx・核・A/Q運搬が完成。
- O_COORDのRun12指定範囲・完備形式級数接錐比較に未完宣言や未証明入力はない。

## 検証・レビュー・公開処理

22ソース・127定理・224core宣言。74fixture宣言も加えた298新規axiom報告、旧443報告、合計741件。
44コマンド、旧55hash（41ソース・11試験・固定環境3）、追加数学公理なし。
新規read-only reviewer `run12_review` は目標1–4のactual閉鎖と全宣言一覧・新規axiom報告を独立確認し、重要な指摘なし。
検証入口は毎回新規ファイル集合と名前付き宣言を再計算し、登録漏れを拒否するよう強化。
数値fixtureの重み表はLean kernelの`decide`と正元表示の長さの補題で認証し、Pythonの数値値を仮定しない。
実行ログ・検証JSON・独立レビュー・受入表・A23–A27・manifest・監査ZIPを同一runの成果として公開する。
正常Push後には実行担当がローカルHEAD/remote work SHA一致とclean worktreeを確認する。コミット自身のSHAを自身の内容に埋め込む循環は作らない。

## Run13への入力と残る全体範囲

入力：actual S₀、全射A/Q、G/T/A/N/Qの作用と次数、actual同jump層のS₀同型・次数差、全terminalの上限、自然な完成環比較。
Run13は20run計画のX_BASIC / I_FIELDを対象とし、Koszul/Tor・有限性・体拡大と通常Bettiへの接続を進める。
Run12でそれらを済ませたとは扱わない。actual安定化・cut/tower/資源・Sidon接続・公刊入力・P14主定理全体も後続。
今回の代替証明は必要な結論を弱めていないため、20run配分の数学的完成条件の変更は不要。
