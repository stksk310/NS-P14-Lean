# Lean Block01–06 監査引継ぎ

2026年11月10日（JST）。このスナップショットは `work` ブランチで公開する。

## 最初に読むもの

1. [現在のLean化進捗](LEAN_PROGRESS.md)
2. [Block01：small scalar](NSP14/Ordinary/SmallScalar.lean)
3. [Block02：Sidon・数値Apéry・scalar接続](NSP14/Combinatorics/Sidon.lean)
4. [Block01の範囲](verification/block01/README_JA.md) と [Block02の範囲](verification/block02/README_JA.md)
5. [V03骨子](proof_structure_v3/P14_PROOF_SKELETON_V03_JA.md) と [依存表](proof_structure_v3/P14_DEPENDENCY_MAP_V03.md)
6. [Block03：資源からSO3](NSP14/Ordinary/Resources.lean) と [式の対応・範囲](verification/block03/README_JA.md)
7. [Block04：rank 2・3の全行数値評価](NSP14/Ordinary/LowRank.lean) と [重み表・範囲](verification/block04/README_JA.md)
8. [Block05：調和和障壁・全大rank基点](NSP14/Ordinary/LargeSeed.lean) と [原稿対応・範囲](verification/block05/README_JA.md)
9. [Leanと最終原稿の対応・変更台帳](docs/LEAN_PAPER_ALIGNMENT_JA.md)
10. [Block06：大rank scalar全域閉鎖](NSP14/Ordinary/LargeScalar.lean) と [有理数シフト・範囲](verification/block06/README_JA.md)

## 特に確認してほしい境界

- `gap_shift` は任意の有理数シフト `s,t : ℚ` の恒等式。
  `small_gap_pos` の正値性は `4 ≤ r ≤ 8`、非負整数シフト `s,t : ℕ`、
  および `r ≤ 5 ∨ s+t ≠ 0` の下で成立する。
- rank6–8の悪い角ではgapが負になることもテストしている。
- Sidon性は同じ項の反復を含む二項和の一意性。差の単射は合成数・偶数のmodulusを許す。
- `AperyPairData` は加法部分モノイドの数値最小元・二項和の最小性・和の一意性を明示した入力。
  actual Q₂の最大性からこのデータを構成する代数的な橋は未実装。
- 境界版のSidon証拠はr≥6かつs=0だけで要求する。内部点へ不要な仮定を加えない。
- Block03は同じ資源列の条件からSO3を証明する。台をcutoff以下に制限しない。
- Block04はrank 2に三角数下限やhead cap M−3を課さない。δ=0を含む。
  rank 3では線形head cap H₁≤3δを明示して要求し、top行も評価する。
- Block05は全r≥9の基点正値性。任意のδ・eへの延長を済ませたとは扱わない。
  原稿から短縮した増分比較は変更台帳A05の証明と照合する。
- Block06でその基点を有理数e≥10・δ≥a_rまで延長した。
  t(t−1)の非負性を有理数へ誤用せず、b₀−(1−α)/2>0を使う。変更台帳A06参照。
- 実際のtowerからその共通資源列を作ること、actual接錐・Tor/Bettiへの接続、P14全体は未完成。

## 再現

Lean `v4.36.0-rc2` とmathlib revisionはtoolchain・Lake manifestに固定してある。
標準のelanを利用できる環境で、リポジトリrootから実行する。

```sh
lake build
python3 scripts/verify_block06.py
```

Block06の検証スクリプトは新ソースの再検査・テスト・15個の公理依存報告と、
Block01–05の回帰テスト・10個、14個、7個、13個、22個の公理依存報告を検査する。
監査の負のシフトの反例とBlock02の仮定検査も実行する。
通常のLean基盤 `propext`, `Classical.choice`, `Quot.sound` 以外の依存を拒否する。
追加の数学公理や `sorryAx` への依存は認めない。

mathlibキャッシュ先へのアクセスが制限される環境では、初回のみ次で依存を取得し、ソースビルドする。

```sh
MATHLIB_NO_CACHE_ON_UPDATE=1 lake update
lake build
```

このクラウドでは公式GitHub配布の固定Leanを `/tmp/ns-p14-lean` に導入した。
同じ環境なら次で実行できる。

```sh
PATH=/tmp/ns-p14-lean/bin:$PATH python3 scripts/verify_block06.py
```

[保存済みBlock06検証記録](verification/block06/verification.json) とログを同梱する。
ローカルで再検証すると所要秒などは更新されるため、厳密な比較対象には監査するコミットを指定する。

[Block01の独立監査](audit/README_JA.md) と [今回の対応記録](docs/BLOCK01_AUDIT_RESPONSE_JA.md) を保存した。
`audit/` と既存ZIPは監査時の記録、`verification/block01/`・`block02/` はBlock01監査修正までの記録。
Block03–05の記録も保持する。今回の公開import追加後の照合対象は `verification/block06/MANIFEST_SHA256.json` とする。

[Block02独立監査](audit/block02/README_JA.md) は条件付き数値ブロックとして合格。
Block03の外部監査は進行中で、Block04の実装検証と区別する。

## 同梱資料

V03、旧証明、二つの紙上置換、Navi別証明、Lean化計画、対応ZIPを保存している。
旧資料があることは現Lean証明の依存にそれらを公理として足すことを意味しない。
コンパイラ本体、`.lake`、生成された`.olean`、Pythonキャッシュ、接続設定や資格情報は含めない。
V03骨子ビルダーの入力指定文は元の添付パスを参照する。必要なら同梱V03 ZIPから元の相対位置へ復元する。
Leanのbuild・検証はその添付指定文に依存しない。
