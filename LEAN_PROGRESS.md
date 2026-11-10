# Lean化進捗

## 最新状態：Run14途中成果（2026年11月10日JST）

Run13は`d8556dc`で完成・Push済み。Run14は未完であり、完了run数へ加算しない。
11個の新規source・1,245行で、actual offset/安定化/有限性、最大Q₂からのSidon、
F/Uの低次数同型、同じactual Hと全tail有限台、H₀=δ、actualLayersを証明した。
Green・同じcut・鋭い体積・truncated tower/生成・全資源条件・actual Dataは未完。

[正確な状態と宣言](docs/RUN14_REMAINING_DECLARATIONS_JA.md)、
[検証](verification/run14/verification.json)、[再校正](docs/RUN14_20RUN_RECALIBRATION_JA.md)。
以下は各段階時点の履歴であり、最新の未完境界は上記文書を優先する。


2026年11月9日（JST）。

| 範囲 | 状態 | 証拠 |
|---|---|---|
|M00の固定環境・初回build|Lean v4.36.0-rc2、mathlib commit固定。ソースから依存build成功|lean-toolchain、lake-manifest.json|
|Block01：O_SMALLの数値部分|コンパイル済み。任意の有理数シフトの恒等式、5行、非負整数シフトと明示した角条件の下での正値性|NSP14/Ordinary/SmallScalar.lean|
|境界・依存監査|全域example、負の3基点、隣接点、10個のaxiom reportが通過|tests/SmallScalar.lean、verification/block01/|
|actual Apéry–Sidon・実対象からの資源構成|未接続。数値資源からSO3への評価はBlock03で実装|後続ブロック、NSP14/Ordinary/Resources.lean|
|M12全体・P14全体|未完了|今回の数値ブロックから全体完了を推測しない|

主定理はsmall_gap_pos、後続の受入口はscalar_lt_of_upper。
新しい数学的axiomやsorryAxへの依存はなく、10個の監査対象の依存は
propext・Classical.choice・Quot.soundだけである。

初回はコンパイラ取得と約2千build jobの依存構築も行った。
保存した最終チェックの所要秒は依存構築後の再検証時間であり、
初回総作業時間や他モジュールの速度を表すものではない。
計画段階の人日見積は、この一つの算術ブロックから全体へ外挿せず、
接錐モデル・Koszul接続の試作後にも再評価する。

## Block02：2026年11月9日（JST）

Sidon差単射、巡回群濃度、数値Apéry最小元、データからのSidon構成、
m≥e(e−1)+1とδ≥(e−1)²、Block01への境界接続をコンパイルした。
14定理のaxiom reportとBlock01の10報告を検査し、追加数学公理はない。
Block01の証明ソースは変更していない。rootの公開importは拡張した。

actual Q₂の最大性からAperyPairDataを構成する橋は未実装。
数値データを実際の半群の最小生成系と一致させること、SO3、Betti接続も残る。
従って「数値・組合せのBlock02とその接続」が完成であり、actual Apéry–Sidon全体の完成ではない。

## Block01監査対応：2026年11月9日（JST）

独立監査は数値ブロックを合格とし、正値性の「全整数シフト」という表記を指摘した。
非負整数シフトと角条件へ表記を修正した。定理の型・定義・証明本体は変更しない。
監査の負のシフトの反例を両ブロックの検証に追加した。
監査原本は `audit/`、修正内容と再検証の範囲は `docs/BLOCK01_AUDIT_RESPONSE_JA.md` に保存する。

## Block03：2026年11月9日（JST）

同じ有限資源列の総量・head cap・tail capから、任意の `n≥r≥4` でSO3を証明した。
列の台はcutoffを越えてよい。新規7定理は残余重みの符号、有限和評価、SO3、
Block01のSO5、Block02の境界Sidon・数値Apéryデータとの合成である。
新しい受入口では `F≤upper` の仮定を要求しない。

実対象のtowerから共通資源を作ること、actual Q₂からApéryデータを作ること、
r=2,3およびr≥9、Tor/Bettiは未完。M12・P14全体の完成ではない。
前二ブロックのソースと固定環境を保持し、今回の検証記録は `verification/block03/` に置く。

## Block04：2026年11月10日（JST）

V02 (7.3) の重みを定義し、O_LOWの数値部分としてrank 2の第一・top行と
rank 3の第一・第二・top行を証明した。rank 2はδ=0を許し、三角数head capを課さない。
総量と線形head cap、rank 3では追加head capから同じ列の全行を評価する。
新規13定理。Block03から列をそのまま搬送し、第一行が既存scalarと等しいことも証明した。

actual tower・Torから重み付き和への移行・actual target余裕・Bettiの接続、r≥9は残る。
検証記録は `verification/block04/`。Block01–03の証明ソース・テストを保持する。

ユーザーからBlock02独立監査の通過報告を受け、リモート監査原本も取得した。
`audit/block02/README_JA.md` の判定は「条件付きの組合せ・数値ブロックとして合格」。
原本の仮定検査をBlock04の回帰に加える。Block03の外部監査は進行中。

## Block05：2026年11月10日（JST）

調和和の障壁をr≥10の帰納で証明し、固定cutoffの基点G_r(10,a_r)>0を全r≥9で証明した。
自然数三角数と有理数cast、cutoffの両側評価、調和和と既存tail和の一致、
閾値との比較、r=9の一行を含む新規22定理。
凸性の中間評価を正係数の四次式による直接の増分比較へ短縮した。

原稿へ戻せる変更を `docs/LEAN_PAPER_ALIGNMENT_JA.md` A05に記録し、
Block04の有理数多項式評価など既存の対応も同じ台帳にまとめた。
基点から任意のe・δへの差分評価と大rank scalarの全閉鎖は次の単位。
actual tower・Tor/Betti・M12・P14全体の完成ではない。
今回の検証記録は `verification/block05/`。Block01–04のソースとテストは保持する。

## Block06：2026年11月10日（JST）

Block05の基点から、全r≥9・有理数e≥10・δ≥a_rのgap正値性を証明した。
Block03の同じ資源列の上界と合成し、`Resources.scalar_lt_large` が大rank scalarを閉じる。
新規15定理。cutoffの偶奇分岐を一つの式に統合し、b₀>5/4へ強化して有理数シフトを扱う。
原稿へ移せる代替証明は対応台帳A06に記録した。

一般のr≥4で全行をscalarへ還元する評価、actual資源構成・Tor・target余裕・Betti接続は後続。
M12・P14全体の完成ではない。検証記録は `verification/block06/`。
Block01–05のソースとテストは保持する。

## Block07：2026年11月10日（JST）

操作頻度を減らすユーザー指定に従い、全行scalar化・target余裕・数値全域統合を一括実装した。
新規3ファイル・25定理。`NumericalClosure.Data.all_rows` は共通有限資源と境界証拠から
全r≥2、1≤k≤rのL_k+重み付き和≤具体的R_kを返す。
rank2のδ=0、top行、三つの悪い角、非自明な数値Apéry境界証拠まで接続した。

target余裕はVandermondeの完全展開を介さず、δ方向の正確な差分と二項係数の単調性で証明した。
原稿に移せる証明と全域統合の仮定は対応台帳A07–A09に保存する。
ordinary側の有限資源を入力とする数値部分の統合であり、actual資源・Tor・BettiやP14全体は未完。
検証記録は `verification/block07/`。Block01–06のソース・テストを保持する。

## Block08：2026年11月10日（JST）

実際のcofinite AddSubmonoid ℕから始め、6ファイル・85定理とterminal/head全単射を構成した。
mは最小正元、Apéryは各剰余の最小元として存在・一意性を証明し、濃度mとω+qm一意分解を得る。
原子の有限性・生成性・任意生成集合に含まれる最小性、actual eと0<e≤mを証明した。
最長orderの存在・超加法性・原子表示との一致、Apéry次数0/1/≥2とδ、order≤δ+1も接続した。
terminal/headの数値全単射とjumpの向きも証明した。

ℕ、⟨3,4⟩、jumpが実際にある⟨6,7,15⟩を検査し、actual m/e付きデータをBlock02へ接続した。
新規85定理と全単射定義1件の公理依存を検査する。既存Block01–07は保持。
actual接錐・商/核との環・加群同定、volume/cut/tower、Tor/Bettiは未完。
原稿対応は台帳A10–A11、検証記録は `verification/block08/`。

## Block09：2026年11月10日（JST）

7ソース・43定理、60宣言。actual代数的半群環の正元イデアルの全冪とorderの係数条件が一致する。
定数項環準同型とactual原子での生成、体上の極大性、次数付き実商の係数同値・有限単項式基底、
商上の双線型積とlive/killed条件、terminalとx乗算の単項式核の同値まで構成した。

完備化との比較と全直和の次数付き環のパッケージ、核全体・A/N/Qの基底、同jump加群同型、
actual塔/資源、Tor/Betti、P14全体は後続。対応台帳A12–A14へ原稿に使える証明を記録する。
検証入口はscripts/verify_block09.py。完成範囲と境界はverification/block09/README_JA.md。

Block09最終検証：19/19コマンド、252公理依存報告、26既存hashが通過。
独立レビューも重要な実装指摘なし。説明の係数環仮定2か所を修正し全検証を再実行した。

## Block10：2026年11月10日（JST）

7ソース・35定理を含む71宣言。実冪の商の全直和を可換k代数へ構成し、全体のactual単項式基底を証明。
xの実乗算をlive係数shiftと同定して核・像全体を構成し、Tのterminal基底とactual環の商A=G/xGのhead基底を得た。
基底とactual単項式の一致、各次数のx作用との一致も証明する。

完備化比較、N/Qの次数付き構成と同jump加群同型、jump上限、actual塔/資源、Tor/Betti、P14全体は後続。
今回の全体の基底の構成を、A全体やterminal集合の有限性の証明と混同しない。
原稿への証明反映をA15–A17へ記録し、検証入口をscripts/verify_block10.pyに更新する。

Block10最終検証：20/20コマンド、323公理依存報告、34既存hashが通過。
独立実装レビューも指摘なし。レビュー担当は新テストの再コンパイルと既存34hashの照合を独立に実行した。

## Block11：2026年11月10日（JST）

12ソース・81定理、計120宣言。Nをactual A全体のidealとして構成し、actual非Apéry head基底と斉次性を証明。
実商Q=A/NからApéry係数同値・基底・積を構成し、Gからの実次数像をregistered gradingへ同定した。
任意体でdim Q=m、q0=1、q1=e−1、q2≤δ、高次総量δ、actual最高次数ν≤δ+1。
自然な商写像A_n→Q_nはn≤2で同型。Qのactual次数1原子による生成とArtin性も証明した。

完備半群環との比較、同jump加群同型、jump≤ν、actual塔・資源、最大Q2からSidonデータ、
S0の多項式表示・Koszul/Torとtarget Betti、P14全体は後続。Qの有限性をA・N・Tすべての有限性と混同しない。
原稿対応台帳A18–A22へ証明順・構成・仮定と新しいνの説明を記録する。

Block11最終検証：26/26コマンド、443公理依存報告、42既存hashが通過。
独立実装レビューは指摘なし。レビュー担当はテスト再コンパイル・42hash・120宣言/reportの一致を独立確認した。
ordinary m=e=3、δ=0、ν=1の追加境界例も含め、実装担当が全suiteを再実行した。

## Run12：2026年11月10日（JST）

22ソース・127定理、計224core宣言。指定されたactual O_COORDと形式級数接錐の比較を閉じた。
単一の非x原子S₀作用をG/T/A/N/Qへ整備し、A/Q全射と次数1生成を証明。
実核Tと実イデアルN上の反対向きの斉次jump filtration、実商のS₀線型同型、同じ写像の実継承次数差sを構成。
全terminalで2≤jump≤actual νを最長表示の切断から直接証明し、δ=0でactual T=N=0も接続した。
literal k[[S]]の実極大イデアル冪を無限級数の係数条件と同定し、代数的Gとの自然な次数付きk代数同値とx・核・A/Qの運搬を証明。

44コマンド、741axiom報告（新規224core+74fixture、旧443）、55既存hashを検査。
独立実装レビューは重要な指摘なし。宣言一覧をソースから再計算する照合も検証入口へ追加。
原稿対応A23–A27、実行台帳、受入条件別のexport表と監査ZIPを同runへ含める。
Run12の数学的目標に未完宣言・未証明入力はない。
20runは目標であり完成条件ではない。X_BASIC全体・安定化・actual資源/cut/tower・Sidon接続・Koszul/Tor・target Betti・P14全体は後続。

検証入口：scripts/verify_block12.py。監査入口：verification/block12/README_JA.md。
Block10外部監査branch `audit/block10-20261110`（28300b47f72df87983c3e1dba10a11da3466032d）の合格も確認済み。
その認証範囲は代数的G/T/Aであり、Run12の追加範囲の独立数学査読とは区別する。

## Run13途中版：2026年11月10日（JST）— 92cbe8fでの歴史的スナップショット

基準Run12 `6b8d168`。`NSP14/Homological/` に全原子最小表示・全次数の斉次性、
実変数Koszul、actual augmentationと有限自由解消、通常mathlib Torとのobjectwise比較、
全変数null-homotopy、有限P生成から有限k homology、totalBettiと自由PのBettiを追加した。
完成接錐・同jump層の通常Tor/totalBetti運搬、実商の標準単項式基底と±1 minorも証明した。

一般短完全複体のH₀/正次数rank補正式、flatな実L⊗ₖ複体のhomology比較と次元保存もある。
ただしgraded Koszul/Betti、Tor比較自然性・極小解消rank/balancing、Koszul短完全列/有界比較、
変更後L[X]加群との自然なbase-change比較は未完。X_BASIC/I_FIELD全体は閉鎖していない。

詳細と宣言境界：`docs/RUN13_EXECUTION_LEDGER_JA.md`、`docs/RUN13_REMAINING_DECLARATIONS_JA.md`。
原稿台帳A28–A33。検証入口 `scripts/verify_block13.py`、`verification/block13/README_JA.md`。
全体20runの再校正：`docs/RUN13_20RUN_RECALIBRATION_JA.md`（暫定24〜28、完成条件は維持）。


## Run13継続完了：2026年11月10日（JST）

指定Task1–8の共通基盤を実装・接続し、全40コマンドの検証を通過した。
core69ファイル・5,895行・named宣言458（theorem217）。環境に存在する生成宣言まで含めてcore1,207/test77を検査し、
旧741レポートと合わせて2,025件の公理依存を確認。許容3公理のみ、旧84 hashと固定環境は一致。

通常Torの自然性、実極小自由解消rank、graded/totalの有限和、actual grading、同jumpのt→t+s、
実Koszul/Tor LES・補正rank・有界filtration、実L[X]作用とactual G/T/A/N/Qのtotal/graded Betti体拡大保存を閉じた。
独立レビューImportant2件も修正し、L側の独立order-gradingとの同定とinclusion可換性まで供給した。
P/(X²)の(1,1,0,…)、残余体binomial、自由P、標数2・非斉次写像・actual例が通過。

入口：`scripts/verify_run13_continuation.py`、`verification/block13_continuation/README_JA.md`、
`docs/RUN13_CLOSURE_STATUS.json`。原稿台帳A34–A40、途中版原本は保持。
最終P14・actual cut/tower・公刊入力は後続run。20runは再校正した目標配分であり達成保証ではない。

## Run14継続完了：2026年11月10日（JST）

途中版8040c90から38 coreファイル・3,112行を追加し、指定Run14の接続を閉じた。
Greenは最大rank pencil/minorと対称・交代積の計数から任意標数で実証明し、全prefix同時のflagを構成。
固定したk(X)上で一つのcutを選び、actual S₀/P作用、actual K≃Run12 stratum、
truncated短完全列、X/M単一次数生成とaugmentation商の実底次数同型まで接続した。

least-offset rankによる鋭いδV、actual区間・剰余内非交差、全mass恒等式、H1+a=δ+ell、
ell≤e−1、同cutからH1≤rδ、全tail capを同じHで証明。
actual DataとSidon Boundaryから既存全行比較へ通る。r=2へ三角数条件を課さない。
歴史的な未完Prop5本も、その型のまま別監査ファイルで証明した。

50検証コマンド、環境3,217宣言・全新規544宣言、許容3公理、旧source/依存/証拠241件を検査。
fresh独立レビューはCritical/Important 0。匿名受入例二本の環境coverage欠落は公開定理化してRED→GREEN。
origin/workで先行したRun13再現性修正aa6bf4cもfast-forwardで保持し、同修正を凍結照合へ追加した。
最終数値と検証時間はverification/run14_continuation/verification.jsonが正本。
原稿対応A44–A49、監査ZIPはCOMPLETE版。旧PARTIAL原本・固定依存は維持。

Run14指定範囲の未完入力はない。actual Tor評価・target Betti同定・ordinaryのactual閉鎖と
最終P14はRun15以降。20runは保証ではなく、再校正した数学的接続ごとの運用目標。
