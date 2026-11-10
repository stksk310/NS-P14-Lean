# Run14途中成果の検証入口

**Run14全体は未完。** `verification.json`のstatusは`PASS_IMPLEMENTED_EXPORTS_ONLY`。
成功したkernel検査からGreen/cut/資源/actual ordinary閉鎖を推測しない。
正確な範囲は`docs/RUN14_CLOSURE_STATUS.json`と
`docs/RUN14_REMAINING_DECLARATIONS_JA.md`を読む。

再実行：固定LeanをPATHに含め、repository rootで

```sh
python3 scripts/verify_run14.py
```

固定環境はRun13と同じLean v4.36.0-rc2、mathlib 139105d。
新しい11sourceと4testを登録し、既存Run13 suiteの全回帰コマンドを再実行。
Run13 commitの旧Lean source・旧test・固定依存を一切変えていないことを内容照合する。
root importは旧内容の末尾追加だけ許可する。

環境監査はNSP14の**全**宣言と新しい受入testを列挙し、constructor/recursor/instance/生成補助も含む。
Lean自身の`collectAxioms`で許容`propext`・`Classical.choice`・`Quot.sound`以外と自己依存を拒否する。
proof-erasure stubのraw種別はexported_kindに残す。新しい数学公理・未証明placeholderのソースguardも実行。
`declarations.json`に通常型とexplicit型を保存し、`SOURCE_SHA256.json`に実際に検査したsourceを記録する。

`offset_red.log`と`sidon_red.log`は最初のmissing-export受入が失敗した記録。
最終の同名受入は成功を要求する。`remaining_goal_types.log`の成功は未完命題の型の正しさのみで、
その命題の証明ではない。`audit/run14/RemainingGoals.lean`はproductionからimportされない。

監査ZIPは`artifacts/NS_P14_LEAN_RUN14_PARTIAL_20261110.zip`。
原本の過去ZIPは埋め込まず、source/検証/原稿台帳/計画/引継ぎとmanifestを収録する。

旧sourceの内容照合はGitの基準commit `d8556dc615b1e1633379f4567e9e795b3f1c8ae3`を読むため、
再実行時にはこのcommitがローカルhistoryに必要。ZIPはGit databaseやmathlib cacheを含めない。

## 今回の最終検査

45コマンドが全て終了code 0。全project環境2,784宣言を列挙し、新規296宣言
（core185・test111）を含め、公理依存は許容3公理内。
旧Lean source/testと固定依存171ファイルはRun13 commitと内容一致。
11新規core source・1,245行。結論は実装済み部分の検証成功であり、Run14の完了ではない。
