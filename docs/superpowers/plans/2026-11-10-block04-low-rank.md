# Block04 Low-Rank Bounds Implementation Plan

> **For agentic workers:** Use superpowers:executing-plans to implement this plan task-by-task.

**Goal:** V03 O_LOWの数値部分としてrank 2・3の全行の重み付き和を評価する。

**Architecture:** `Layers` は非負のheadと有限台付きtailを持つ。V02 (7.3) の重みを定義し、同じ列の総量・head上界から§9の全行評価を証明する。rank 2にδ≥3や三角数head capを要求しない。

**Tech Stack:** 固定Lean v4.36.0-rc2 / mathlib既存revision。

**Spec:** `proof_integrated_v2/NS_P14_INTEGRATED_PROOF_JA.md` §7 (7.3), §9；`proof_structure_v3/P14_PROOF_SKELETON_V03_JA.md` III.1 O_LOW。

## Global Constraints

- Block01–03の証明ソース・テスト・固定依存を変更しない。
- 追加数学axiom・sorry・上界そのものを仮定するplaceholderを導入しない。
- actual Torから(7.3)への移行、actual towerから資源構成、target余裕(8.4)の証明は後続工程。
- ユーザー指定どおり現行workへ検証後Pushする。Block02の外部監査通過はユーザー報告として記録する。

## Review Focus

rank 2のδ=0、V=3の分岐境界、任意に遠いtail、rank 3のδ=6、top行を含むこと。
rank 2で三角数head capを暗黙に使わず、head≤2δだけを追加条件とする。

### Task 1: 有限層と低rankの全行評価

**Files:** `NSP14/Ordinary/LowRank.lean`, `tests/LowRank.lean`, `NSP14.lean`。

**Interfaces:** `Layers.row` は(7.3)の重み付き和。rank 2で第一行とtop行、rank 3で第一・第二・top行の評価を返す。
`Resources.toLayers` でBlock03の同じ列を搬送し、rank 3へ接続する。

- [x] 公開インターフェースのテストを書き、実装前に存在しないことを確認する。
- [x] 重みの有限和評価、V≤3/V≥3の分岐、rank 3の多項式余裕を証明する。
- [x] 空塔・境界・遠い台と全行の受入口を検査する。

### Task 2: 検証・監査・Push

**Files:** `scripts/verify_block04.py`, `verification/block04/`, 監査ZIP、README/progress/handoff。

- [x] 新規定理の全公理依存とBlock01–03の回帰、負のシフト検査を実行する。
- [x] 別担当に式・添字・仮定のレビューを依頼し、原稿対応・未完の接続を記録する。
- [ ] manifest・ZIPを照合し、コミット・Push後のremote SHAを確認する。

## 実装判断

rank 2へBlock03 `Resources 2`を直接要求すると、不要なhead cap M−3を課してしまう。
そのためhead capを含まない `Layers` を用い、rankごとに必要な条件だけ受け取る。
rank 3ではBlock03からこの型への単純な射影を用いる。

## 実行記録

基点は `ff69aecb56433881f72f926883ab1701a732d5cd`。
Task 1完了：実装前のインターフェース不在を確認し、実装後のテストが通過した。
Task 2検証完了：8コマンドの終了コード0、公理依存13+10+14+7件は標準基盤のみ。
別のレビュー担当も原稿と照合し、テストを独立実行した。正しさに関する指摘なし。
監査記録は `verification/block04/REVIEW_JA.md`。
Block02の監査原本の取得後、その仮定検査を追加して8コマンドを再実行した。
