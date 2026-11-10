# Lean化進捗

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
