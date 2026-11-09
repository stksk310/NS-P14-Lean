# Lean化進捗

2026年11月9日（JST）。

| 範囲 | 状態 | 証拠 |
|---|---|---|
|M00の固定環境・初回build|Lean v4.36.0-rc2、mathlib commit固定。ソースから依存build成功|lean-toolchain、lake-manifest.json|
|Block01：O_SMALLの数値部分|コンパイル済み。任意の有理数シフトの恒等式、5行、非負整数シフトと明示した角条件の下での正値性|NSP14/Ordinary/SmallScalar.lean|
|境界・依存監査|全域example、負の3基点、隣接点、10個のaxiom reportが通過|tests/SmallScalar.lean、verification/block01/|
|actual Apéry–Sidon・SO3資源上界|未接続。明示した仮定として残る|後続ブロック|
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
