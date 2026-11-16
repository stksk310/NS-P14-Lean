# Block05 Harmonic Barrier and Large Seed Implementation Plan

> **For agentic workers:** Use superpowers:executing-plans to implement this plan task-by-task.

**Goal:** r≥9の全rankで固定cutoffの基点G_r(10,a_r)>0を閉じる。

**Architecture:** 三角数の自然数版とcast、D_r=⌊a_r/2⌋+1、有限調和和を定義する。一般項の単純上界からHの増分を抑え、B(r)=r/4+1+9/(2r)との比較を正係数四次式で帰納する。原稿のT₁とBの正の差を証明し、既存gapへの恒等式で全基点正値性を得る。

**Tech Stack:** 固定Lean v4.36.0-rc2 / mathlib revision。依存revisionの変更なし。

**Spec:** V03 III.5 O_LARGE (O21)；V02 §11 (S2), (S6)–(S20)。

## Global Constraints

- Block01–04のソース・テスト・固定環境を保持する。
- sorry・追加数学axiom・未証明の調和和上界を導入しない。
- r=9は正確な有理数基点、r≥10は数学的帰納で閉じる。有限サンプルで無限域を代用しない。
- 基点から任意のe,δへの差分・正値性、actual tower・Tor・Bettiは次の接続単位。
- 検証・レビュー後、ユーザーの継続Push許可に従ってworkへPushする。

## Review Focus

自然数三角数の除算と有理数三角数の一致、cutoffの偶奇、調和和の添字、r=9/10境界、r≥10の帰納。

### Task 1: 調和和・cutoff・障壁

**Files:** `NSP14/Ordinary/LargeSeed.lean`, `tests/LargeSeed.lean`, `NSP14.lean`。

- [x] 公開受入口の不在を確認し、三角数castとcutoff範囲を証明する。
- [x] 調和和の増分≤(r+2)/(a_r+3)と、これがBの増分より小さいことを証明する。
- [x] H_{D_r}<B(r)とB(r)<T₁(r)≤T_rを証明し、r=9を含む基点を閉じる。

### Task 2: 検証・監査・Push

- [x] 新規公理依存とBlock01–04回帰、既存監査検査を実行する。
- [x] 独立レビュー、紙上対応、未完範囲、manifestと監査ZIPを保存する。
- [ ] 検証済み変更をコミット・Pushしremote SHAを確認する。

## 実装判断

原稿の凸性による細かい増分評価の代わりに、全項≤1/(D_r+1)という粗い上界を用いる。
Bの増分との差の分子はx=r−10≥0に対してx⁴+34x³+385x²+1472x+112>0。
同じ障壁・同じ基点を得る局所的な証明短縮であり、別の有限証書ルートを導入しない。

## 実行記録

基点commitは `66e92970f9469a73db073dfc7da5b71800e5484e`。
Task 1完了：新規22定理をコンパイルし、自然数除算・境界・普遍受入口のテストが通過した。
Task 2検証：9コマンドが終了コード0、公理依存66件は標準基盤のみ。
独立レビューのソース再検査とテストも通過し、正しさの指摘はない。
原稿用の基点分数値の提案を受け、等式テストと台帳へ追記して全検証9コマンドを再実行し、通過した。
ユーザーの新方針を `docs/LEAN_WORKFLOW.md` と `docs/LEAN_PAPER_ALIGNMENT_JA.md` に保存した。
