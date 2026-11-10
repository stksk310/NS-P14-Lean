# Run15 COMPLETE版の監査入口

現在の判定は `RUN15_CLOSURE_STATUS.json`、実検証は
`verification/run15_closure/verification.json`、最終ソースレビューは
`RUN15_CLOSURE_REVIEW_JA.md` を参照する。過去のPARTIAL記録・ZIPはそのまま残した。
初回の `RUN15_FINAL_REVIEW_JA.md` は初回部分成果のレビューであり、今回の認証ではない。

## 最短の証明追跡

1. `audit/run15/RemainingGoals.lean` の元の8命題を読む。
2. `audit/run15_closure/ClosedGoals.lean` の `all_original_goals_closed` を読む。
   型を弱めたり、未証明の入力を付けたりせず、元の8命題を同時に閉じている。
3. 一般APは `ArithmeticSequence/BettiFormula.lean` の
   `semigroup_totalBetti`、`cone_totalBetti`、`completed_AP_totalBetti`。
   実核のTor写像消滅は `ModelKernelDivision/ModelTorClosure`、有限商の実計算は
   `WindowHankel/WindowBetti`、環表示の同定は `ModelHeadBetti/ModelKernelBetti`。
4. ordinary主定理は `Ordinary/Closure.lean` の
   `ordinary_actual_completion_betti_le`。元の任意体、全行、literal完成sourceと
   interval target、各自の実最小表示で比較する。
5. `RUN15_CLOSURE_LEDGER_JA.md` から各前提の供給元を追う。
   原稿変更は `LEAN_PAPER_ALIGNMENT_JA.md` A55–A73。

## 再検証

履歴と固定依存を持つ通常のリポジトリcheckoutで、指定toolchainを利用して実行する。

```bash
python3 scripts/verify_run15_closure.py --fresh-test-cache
python3 scripts/package_run15_closure_audit.py
```

verifierは固定基準 `33079c170d038eddb432584837035566ae3577ae` までの
数学・受入・監査・スクリプト・検証・ZIP原本を照合する。全fixtureを依存順で実行し、
既存数値回帰も実行する。全project宣言の公理依存を調べ、Run15全差分について
通常型・explicit型・所属moduleを `declarations.json.gz` に保存する。
許容公理は `propext`、`Classical.choice`、`Quot.sound` の3種だけ。

全production/tests/audit Lean、固定環境、検証/packager、数値checkの入力を
SOURCE_SHA256に結び、検証中・検証後のsource変更を拒否する。
packagerは証明検査PASSと、別途レビューPASS、現在のCOMPLETE statusを要求する。
ZIP全entryのmanifest照合とCRC検査を実行する。

ZIPは監査用snapshotであり、`.git`履歴やmathlib binary cacheを同梱した環境ではない。
再実行は上記の通常checkoutで行う。検証実行時間や一時cache退避先は環境ごとに変わる。

## 境界

今回閉じたのはRun15の範囲。狭幅targetの公式は得たが、狭幅sourceの主比較は
Run16–20で閉じる。GSSの元の解消を形式化したとは主張せず、必要なBetti公式を
別の実Koszul計算で証明した。独立した公開後の監査を、この内部レビューで代替しない。
