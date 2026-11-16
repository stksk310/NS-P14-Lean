# Block06 Large-Rank Scalar Closure Implementation Plan

> **For agentic workers:** Use superpowers:executing-plans to implement this plan task-by-task.

**Goal:** Block05の基点を全r≥9、e≥10、δ≥a_rへ延長し、Block03から大rank scalar不等式を導く。

**Architecture:** 基点のe係数Aとδの最初の差分b、補正Cを既存gapから定義する。床関数の下限を連続的に用いて偶奇の分岐を除き、r≥9ではb>5/4という強い下界を示す。二変数恒等式を非負の有理数シフトへ拡張し、同じResourcesの上界と合成する。

**Tech Stack:** 固定Lean v4.36.0-rc2 / mathlib revision。

**Spec:** V02 §11 (S21)–(S31)、V03 III.5 (O22)–(O23)、Block03・05。

## Global Constraints

- Block01–05のソース・テスト・固定環境を保持する。
- sorry・追加数学axiom・仮定したgap正値性を使わず、証明済みBlock05から導く。
- 原稿からの改善を `docs/LEAN_PAPER_ALIGNMENT_JA.md` へ記録する。
- actual資源構成・Tor・Betti・r≥4の全行scalar化は今回の範囲外。
- 検証・独立レビュー後、workへPushする。

## Review Focus

r=9、δ=a_r、e=10、cutoffの両偶奇、0<t<1の有理数シフト。
自然数のt(t−1)≥0を有理数へ誤用せず、線形係数b−(1−α)/2の正値性を証明する。

### Task 1: 差分・係数の正値性

**Files:** `NSP14/Ordinary/LargeScalar.lean`, `tests/LargeScalar.lean`, `NSP14.lean`。

- [x] 公開インターフェースの不在を確認する。
- [x] g₀=(a+9)A+C、b=A+11−r−8αとC<0を証明する。
- [x] floorの下限からb>5/4を示し、有理数シフトで正となる二次式へ整理する。
- [x] 全r≥9のgap正値性をResources.scalar_lt_largeへ接続する。

### Task 2: 検証・記録・Push

- [x] 新規公理依存とBlock01–05回帰、既存監査検査を実行する。
- [x] 別担当に原稿・式・仮定と対応台帳をレビューしてもらう。
- [ ] manifestと監査ZIPを保存し、コミット・Push後のremote SHAを確認する。

## 実行記録

基点commitは `542b19ec5ce3f4728ccd314b3598ce09d0b51cb6`。
Task 1完了：新規15定理をコンパイルし、有理数シフトと資源接続のテストが通過した。
Task 2検証完了：10コマンドが終了コード0。公理依存81件は標準基盤のみ。
別担当もソースとテストを独立実行し、原稿対応台帳A06を照合した。指摘なし。

実装判断：原稿のb>1/4に代わりr≥9でb>5/4を使い、二次式の負の一次項を吸収する。
同じ結論を有理数e,δへ強化し、偶奇を一つのcutoff比較に統合した。
この数学的な変更と原稿反映事項は `docs/LEAN_PAPER_ALIGNMENT_JA.md` A06に保存した。
