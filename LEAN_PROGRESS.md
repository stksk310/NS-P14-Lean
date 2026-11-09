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
