# Block03 Resource-to-SO3 Implementation Plan

> **For agentic workers:** Use superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox syntax for tracking.

**Goal:** 同じ有限資源列からSO3を証明し、Block01・02のscalar接続へ渡す。

**Architecture:** `Resources r e d` はH₁、H₂以降の有限台付き列、非負性、総量、head/tail capを保持する。一般cutoff n≥rで重みからαを引き、非正のtailを落とす普遍的な有限和評価を証明する。cutoffによって資源列の台を制限しない。

**Tech Stack:** 既存固定Lean v4.36.0-rc2 / mathlib revision。依存変更なし。

**Spec:** `auditability_search/ORDINARY_PAPER_REDUCTION_JA.md` §2 (SO3), §3 (SO5)、既存Block01・02。

## Global Constraints

- 定義・定理・証明にsorry、追加数学axiom、未証明の上界仮定を導入しない。
- actual接錐からの資源列構成・actual Q₂からのApéryデータ構成・Tor/Bettiは後続工程。
- 既存監査原本とZIPを変更しない。現行記録と履歴の区別を保つ。
- ユーザーの「そのまま次のBlock」の指示に従って現行workで実装し、検証後Pushする。

## Approaches

列の長さをcutoffに固定する方法は長いtailを失うので採用しない。
Finsuppによる全列も可能だが、今回は有限台Finsetと台外ゼロの証明を持たせる。
これは実装者の選択で、論文の有限資源列を明示し、既存の有限和APIで証明を短く保てる。

## Review Focus

cutoff未満の空tail、cutoff一致の重み0、cutoff超の正の資源、任意に遠い台を扱う。
同じ資源列を総量と各capの双方に使う。r=6–8の角条件を無条件に削らない。

### Task 1: SO3と接続

**Files:** Create `NSP14/Ordinary/Resources.lean`, `tests/Resources.lean`; modify `NSP14.lean`.

**Interfaces:** `Resources.scalar_le_upper` は `4≤r`, `r≤n` の下でSO3を返す。
`Resources.scalar_lt` は自然数シフトと角条件、境界Sidon版・Apéry-pair版は対応する証拠を受け取る。

- [x] テストに公開インターフェースとcutoff超の台の例を書き、実装前の不在を確認。
- [x] 残余係数の符号、有限和評価、SO3、Block01・02との接続を証明する。
- [x] 空tail・cutoff一致・cutoff超をLeanで検査する。全新規普遍定理の公理依存を確認する。

### Task 2: 検証と監査引継ぎ

**Files:** Create `scripts/verify_block03.py`, `verification/block03/`; update README/progress/handoff.

- [x] Block03のbuild・ソース再検査・テスト・Block01/02回帰・負のシフト検査を実行する。
- [x] 紙上式との対応、合格範囲、残るactual接続、ソースhashを記録する。
- [ ] 差分をレビューし、検証済みの変更をコミット・Pushしremote SHAを確認する。

## 実行記録

基点commitは `6adb7373a72ff3179883549ba6af36cd8608eb82`。
Task 1完了：実装前の不在を `interface_before.log` で確認し、実装後の全テストが通過した。
Task 2検証完了：`python3 scripts/verify_block03.py` の6コマンドが終了コード0。
公理依存7+10+14件は標準基盤のみ。独立レビュアーの式・仮定照合とテスト再実行も合格。
レビュー記録は `verification/block03/REVIEW_JA.md`。

実装判断：Finsuppの代わりに台外ゼロ付きのFinsetを採用した。数学的な有限性は同じであり、
台の選択で非零層が落ちる危険は `tail_vanish` で排除する。
将来API変更が必要ならこの表示を変換する費用が生じるが、証明範囲には影響しない。
