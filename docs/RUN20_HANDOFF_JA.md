# Run20 / P14最終統合 引継ぎ

採用base: `07fe1ed952ae31ce01255ce53df538bf0a76d5cc` (Run19通常公開)。原workspaceの.gitはread-onlyのため `/tmp/ns-p14-run20-20261116` に独立clone、borrowed objectなし、既存Run19 source/cacheは不変。

公開入口: `NSP14.NumericalSemigroup.p14_totalBetti_le_intervalCompletion`。
引数はS・k・[Field k]・iのみ。双方のFormalTangentAlgebra、双方独自のAtomExponent/FullPolynomialRing、literal intervalCompletionAllを使う。最小importは `NSP14.Main`。全域排他的分割は `parameter_partition`。凍結受入は `audit/run20/acceptance/I_PARTITION.lean` と `I_MAIN.lean`。

数学・原稿対応は `RUN20_PAPER_CORRESPONDENCE_JA.md` と50-ID JSON。認証は新規 `verification/run20/runs/*/verification.json`、同source/evidence manifest、review本文/decision、配布ZIP/publication receiptを一つのproof SHAへ照合する。このhandoffやstatusの文字列だけではCOMPLETEではない。

再現:

```sh
PATH=/path/to/pinned/lean/bin:$PATH python3 scripts/verify_run20.py --fresh-project-cache --output-dir verification/run20/runs/independent_unique
```

固定Lean/mathlibとGit履歴が必要。project lib/IR/tests/auditsはcold、mathlib package cacheは保持。任意 `--baseline-cache <base checkout>/.lake/build` は元sourceの同一性を検査して隔離先へコピーする。依存cacheを含まない監査bundleを完全offline checkoutとは呼ばない。

最終独立レビューは全差分・Main意味・Run19/V06必要入力・全private宣言・verifier/guards/packager・全raw証跡を対象とする。修正後は必要な再検証と新snapshotに戻る。source-bound台帳は凍結後変更しない。最終status/review/Pushは別Git bytesに束縛する。


型監査のexplicit欄は、全argument/universeを含むLeanの完全kernel表示（binder名のみ一意にalpha正規化）である。元kernel型と通常Meta.ppExpr型も全宣言に併記し、各宣言でalpha同値を検査する。Main三出口は標準pretty-explicitも保持する。九つの実Lean encoding controlsと、固定15,774名の被覆/全private importにより表示負荷を数学的被覆の削減へ置き換えない。

最終のexplicit記録はLean.Expr.DAG.v1へ圧縮し、共有subexpressionを参照する。表示省略はせず、JSONから各nodeを実際に再構築し、全宣言で厳密な型一致を検査する。Name成分・universe・binderInfo・変数index・let・literal・projectionを保持、metadata snapshotも同梱。通常型/標準Main pretty表示はそのまま保持。逐次記録・fresh printer cache・最大2workerでメモリ上限を守る。
