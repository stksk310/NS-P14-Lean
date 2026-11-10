# Run13 監査P2修正・再検証

2026年11月10日（JST）。基準：`d8556dc615b1e1633379f4567e9e795b3f1c8ae3`。
**`RUN13-P2-VERIFY-ORDER`は修正・再検証済み。**

[独立監査](https://github.com/stksk310/NS-P14-Lean/blob/audit/block13-20261110/audit/block13/README_JA.md)で、
最終検証が試験の`.olean`キャッシュに依存する問題を指摘した。
ユーザーの指示により監査側で最小修正を適用した。

## 変更

`scripts/verify_run13_continuation.py`の2箇所を修正した。

- buildでNSP14に加え、試験がimportする`Mathlib.Algebra.Field.ZMod`と`Mathlib.FieldTheory.RatFunc.Basic`を明示する。
- Run13受入を実行する際は、共通fixtureの`tests/Run13Fixtures.lean`を先にコンパイルする。

数学的な証明、固定環境、Run14の実装は変更していない。
Run13提出時の`verification/block13_continuation/`、途中版の記録、既存ZIPも保持した。
このディレクトリが修正後の実測記録である。
`SOURCE_SHA256.json`は修正済みスクリプトを含む92ファイルのhashを記録する。
提出時の同manifestとの差は当該スクリプトの1件だけである。

## RED → GREEN

実行中のRun14と別のworktreeを、基準Run13 commitから作成した。
数学ライブラリのbuildキャッシュは利用し、projectの全試験のbuild済みファイルは除いてから検証した。

- 修正前、fixtureをimportする受入は`unknown module prefix 'tests'`で失敗した。
  [失敗ログ](clean_test_red.log)と[開始状態](starting_state.json)を保存した。
- 修正後はコピーではなく、実際の`scripts/verify_run13_continuation.py`をそのまま実行した。
  [全40コマンド](verification.json)がexit 0、警告なし。
  新規17受入、旧Block01–12回帰、全新規宣言、公理依存、過去の境界監査、計画検査が通過した。
- 最初のRun13受入は`Run13Fixtures`であり、その後に依存する受入を実行した。
  [通しログ](console.log)で実行順を確認できる。
- core 1,207・受入77、計1,284宣言の型と公理依存の記録は、基準Run13の提出記録とバイト単位で一致した。
  旧741件も再検査した。依存は`propext`・`Classical.choice`・`Quot.sound`のみで、追加数学公理なし。
- 元の検証入口は標準ディレクトリへ出力するため、今回の実測結果をこのディレクトリへ保存した後、元の提出記録を復元した。

固定Lean `4.36.0-rc2`（commit `b35cb10cf2ced51a2fd1880cfdbf75c71ab7a35a`）、
mathlib `139105d28c7685a154cb3093f79edb2e16708099`で実行した。
判定：[resolution.json](resolution.json)。

## 再現

固定依存を用意したRun13修正後のcheckoutで、試験のbuildキャッシュがない状態から実行できる。

```sh
python3 scripts/verify_run13_continuation.py
```

将来のRun14以降のソース集合はRun13検証の対象ではないため、過去Runの再現にはそのRunのcommitを固定する。
この修正は監査で指摘したRun13のP2を解消するもので、actual cut/tower等の後続証明やP14全体の完成を意味しない。
