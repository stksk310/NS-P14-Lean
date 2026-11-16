# Run14 検証の絶対出力パスを修正

2026年11月10日（JST）。対象：`fbfa5debe3daa115b610ecc72dedc8fd52a817ca`。
監査で再現した`RUN14-P2-ABSOLUTE-OUTPUT-PATH`を修正した。

`verify_run14_continuation.py`は旧検証記録のcommandを再利用する。
fixtureの依存順は修正されていたが、`-o`には実行元の
`/workspace/NS-P14-Lean/.lake/build/lib/lean/tests/...`が残っていた。
別checkoutではそこでfixtureを生成しても、consumerは自身のbuild領域を探すため失敗する。

別worktree・空のproject test cacheで、buildと旧13試験の計14コマンドが成功した後、
`predecessor_13`（JumpBounds）がRun12Fixtures.olean欠落で停止した。
[失敗ログ](relocated_checkout_red.log)を保存した。

修正は、過去のLean commandの出力先だけを、現在のrootとsource pathから
既存`compile_test`で作り直すもの。数学的ソース・旧検証原本・既存ZIPは変更していない。

修正済みの実スクリプトを`--fresh-test-cache`で実行し、[50/50検査](verification.json)がexit 0、警告なしで通過した。
全3,217環境宣言の公理依存と、新規544宣言の明示型・所属等の記録は、対象commitの提出記録と一致した。
許容依存は`propext`・`Classical.choice`・`Quot.sound`のみ。
これは検証手順修正の記録であり、Run14全体の独立数学監査結果とは区別する。

スクリプトの標準出力先で得た結果をここへ保存してから、提出時の
`verification/run14_continuation/`を復元した。
`SOURCE_SHA256.json`の提出時との差は修正スクリプト1件だけである。
[通しログ](console.log)・[修正判定](resolution.json)を保存した。

固定Lean `4.36.0-rc2`、mathlib `139105d28c7685a154cb3093f79edb2e16708099`を使用した。

```sh
python3 scripts/verify_run14_continuation.py --fresh-test-cache
```

再現にはRun14修正後のcommitを固定する。Run15以降の新規source集合は、このRun14検証の対象ではない。
