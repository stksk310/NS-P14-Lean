# Block07 Ordinary Numerical Closure Implementation Plan

> **For agentic workers:** Use superpowers:executing-plans to implement this plan task-by-task without user check-ins between internal tasks.

**Goal:** ordinary側の数値評価を、全cut rank・全行・具体的target容量への一本の定理へ統合する。

**Architecture:** 一般重みのscalar支配、target余裕の二項係数評価、既存の低rank・小rank・大rank閉鎖を統合する。共通の有限層と資源条件から、明示した境界Sidonまたは数値Apéryデータの下で全行の容量比較を返す。小補題は内部単位とし、まとまった到達点まで自律実行する。

**Tech Stack:** 固定Lean v4.36.0-rc2 / mathlib revision。

**Spec:** V02 (7.3), (8.2)–(8.4), §9–11；V03 O_SCALAR/O_LOW/O_SMALL/O_LARGEの数値部分。

## Global Constraints

- Block01–06の証明ソース・テスト・固定環境を保持する。
- sorry・追加数学axiomを使わず、既存の条件付き補題を実際に合成する。
- actual tower・Tor・targetのBetti公式自体は未実装として明示する。
- 原稿との差分を対応台帳へ保存する。
- 数学的な到達点まで実行し、全検証・独立レビュー後にPushする。

## Review Focus

top行、k=1/2、r=4、tailの最初の層、δ=0のrank2、r=6–8の角、任意の有限台。
rank2に三角数条件を課さない。target余裕を結論として仮定せず二項係数から証明する。

### Task 1: 全行scalar化

**Files:** `NSP14/Ordinary/Scalarization.lean`, `tests/OrdinaryNumerical.lean`。

- [x] 二項係数の隣接関係から正規化重みを同定する。
- [x] r≥4の全層・全行について第一行scalarによる支配を証明する。

### Task 2: target余裕

**Files:** `NSP14/Ordinary/TargetMargin.lean`。

- [x] R_j(δ+1)−R_j(δ)=(e+δ) choose(δ+r−1,j−1)を証明する。
- [x] δ方向の帰納と二項係数の単調性から(8.4)を導く。

### Task 3: ordinary数値全域の統合

**Files:** `NSP14/Ordinary/NumericalClosure.lean`。

- [x] 同じ有限層の資源条件からrank2/3、4..8、9以上を空隙なく統合する。
- [x] 境界Sidon・数値Apéry入口を接続し、具体的R_jに対する全行比較を返す。

### Task 4: 検証・監査・Push

- [x] 全新規定理の公理依存、全既存Blockの回帰、境界例を検査する。
- [x] 独立レビューと原稿対応を保存し、manifest・ZIPを照合する。
- [ ] コミット・Pushしてremote SHAを確認する。

## 実行記録

基点commitは `14ebc6d0085f48541cbd96f6abc09728ecdfbcc0`。
Task 1–3完了：3証明単位を実装し、25の新規普遍定理と全域統合をコンパイルした。
Task 4検証：13コマンドが終了コード0、公理依存25+81件は標準基盤のみ。
別担当が3ソースと統合テストを独立に実行し、原稿・対応台帳を照合した。正しさの指摘なし。

実装判断：target余裕をδの差分と二項係数単調性で証明し、Vandermondeの余剰項展開を不要にした。
原稿へ移せる証明は対応台帳A08へ保存する。既存のactual入力を証明済みと読み替えない。
ユーザーの操作頻度を下げるため、内部Task間では指示待ちにせず統合・検証まで継続した。
