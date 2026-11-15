# V06 Lean経路同期 実装計画

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development or superpowers:executing-plans. 今回は既に承認された添付指令を実行し、数学四領域と検証基盤を独立分担する。

**Goal:** Run18六契約と公開型を保存し、紙上V06の五つの短い経路をactual consumerまで形式化する。

**Architecture:** 既存の全j評価・整数性・同一資源を再利用する。旧停止計算APIや強い独立定理は保持し、主証明のproof本文と必要なimportだけを変更する。旧Run18検証器は変更せず、固定base・有限許可リスト・独立証跡を持つ新検証器で認証する。

**Tech Stack:** Lean v4.36.0-rc2、mathlib 139105d28c7685a154cb3093f79edb2e16708099、Python標準ライブラリ。

**Spec:** `docs/superpowers/specs/2026-11-15-v06-alignment-order-input.txt`（今回の添付とbyte一致）。

## 固定条件

開始時origin/workは **a7504eea25f02728d1be6cd0082e8484d639dbe2**。事前指定345e2d82以後の変更はRun19計画とV06原稿・N4引継ぎの追加で、既存Leanには重複変更がない。V06 ZIPも現在のworkに存在しSHA256は `788e4c75c572af8a09fc14de5327417b584b7d3b5725d6496bb9445e2c331f4d` で一致した。

原workspaceのwork/c4fd815と添付・既存成果を保存し、`/tmp/ns-p14-v06-alignment-20261116`、`align/v06-20261116`で実装する。数学五項目以外、ordinary一般恒等式、N4、Run19/20、全P14合成は今回の対象外。禁止項目・固定RequestedGoals・全actual source/target・各自の最小変数・任意体・全行を維持する。今回用の有限変更許可は `V06_ALIGNMENT_CHANGE_POLICY.json` に固定する。

## レビュー重点

- endpointは全jの元の競合集合を保ち、個別主経路のimport閉包からStoppingを除く。旧有限計算枝は引き続き通す。
- first-rowはh=4、h=5のt=2非unit例、u=8を整数slackで扱い、強い厳密presentationに依存しない。
- higherはactual第二行比較ではなく同じ有理資源Bの第二行支払いを使い、i=eでも0除算しない。
- denseは同じ一つのL/Kを保持し、q4t3の等号と最上端j=q+1を通す。q3を広げない。
- 検証器の証拠保存・出力拒否・改変旧moduleの全宣言coverage・型互換性をnegative controlsと独立レビューで検査する。

## Task 1: Endpoint

- [ ] CompetitorBounds/CarrySums/FiniteSocleBounds/FiniteCompetitorsの四箇所を仕様どおり修正する。
- [ ] `tests/V06Endpoint.lean`で既存公開型と全j・境界を検査する。
- [ ] RowPackage/SocleBounds/Width.Closureの個別import閉包と旧停止APIを検査する。

## Task 2: 整数slack第一行

- [ ] `Width/IntegerPayment.lean`に二つの有理仮定→整数上界を証明する。
- [ ] AntipodalComparison/FiveNonAntipodalのactual第一行を分岐のない新補題に接続する。
- [ ] `tests/V06IntegerPayment.lean`にh4・h5nonunit・算術境界を入れる。

## Task 3: 共通higher

- [ ] `Width/HigherFromSecond.lean`にnormalized capacity補題と同じBのactual wrapperを構成する。
- [ ] FiveHigher/SparseHigherの公開型を保持し、新wrapperへ接続する。
- [ ] `tests/V06HigherFromSecond.lean`でe2u2B2/e5u8B14/e5u9B81/4とtopを検査する。

## Task 4: Dense二枝

- [ ] DenseLexResourcesに全core行とt2/t≥3の二条件を同じexistsKで返すhelperを追加する。
- [ ] DensePaymentにt≥3統一係数と支払いを証明し、旧公開型を互換wrapperで保存する。
- [ ] DenseComparisonを直接新helperへ接続し、`tests/V06Dense.lean`で等号/topを検査する。

## Task 5: 固定認証・公開

- [ ] 全新moduleをumbrella末尾に登録、原稿対応と引継ぎを記録する。
- [ ] 新verify/package/controlスクリプト、根別route検査とRouteChecks fixtureを作る。
- [ ] proof commitを固定し、全project cacheを隔離退避してmathlib以外を再構築する。
- [ ] R16の280コマンドを新出力先へ写像して全部再実行し、新fixture/型/公理/依存/negative controlsを追加する。
- [ ] 四数学領域と検証器の独立レビューを行い、指摘修正時は新proof commitで検証をやり直す。
- [ ] source/evidence/reviewの整合を確認した一意の新ZIPを作り、通常Pushする。全五項目がactual consumerまで閉じた場合にのみV06_ALIGNMENT_COMPLETEとする。
