# Run15部分実装の検証入口

**この検証の成功はRun15 COMPLETEを意味しない。**
ordinaryのactual Tor→target Betti→任意体全行閉鎖は未証明。
確定した判定と型は `docs/RUN15_CLOSURE_STATUS.json`、
`docs/RUN15_REMAINING_DECLARATIONS_JA.md`、`audit/run15/RemainingGoals.lean` を参照。

固定Lean/mathlibを用意した通常のリポジトリcheckoutで：

```sh
python3 scripts/verify_run15.py --fresh-test-cache
```

- source基準fbfa5de、再現性修正を統合した固定基準20aadbf。過去source、依存、scripts、verification、ZIPをbyte単位で保持する。
- project test cacheを退避して空にし、全testsを実import依存順で再コンパイルする。過去checkoutの絶対`-o`は再利用しない。
- 試験専用mathlibをbuildし、数値回帰、過去監査型/ClosedGoals、新規監査型も検査する。
- rootをimportしたLean環境から、全project宣言の公理依存を列挙する。新規の通常型・explicit型、instance、private helper、自動生成宣言、constructor/recursorも保存する。
- 許容公理はpropext、Classical.choice、Quot.soundだけ。未完Goalは命題の定義であり証明ではない。

`verification.json` が最終の実行記録。`declarations.json.gz` に宣言型と公理、
`environment_axioms.log.gz` にLeanからの原出力、`SOURCE_SHA256.json` に実検証対象のhashを保存する。
`*_red.log` と `full_regression_attempt_01.log.gz` は開発中に実際に観測した失敗記録。
失敗した旧attemptを最終PASSの代わりに使わない。

監査ZIPはsource/evidence snapshotであり、git履歴・mathlib・Lean本体は含まない。
上記再現には基準commitの履歴を持つ通常cloneと固定依存が必要。
