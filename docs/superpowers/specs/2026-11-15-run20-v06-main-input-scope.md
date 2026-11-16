# Run20 V06主定理指令：入力と設計範囲

2026-11-15 JST。ユーザーの依頼はRun20指令書の作成であり、このスレでのRun20実装開始ではない。

## 最新workと先行作業

明示fetchしたorigin/workは `04906ede0e9e3a04b9c07c791c1e1c49834dd3e1`。既存Run19準備 `306df7b` からfast-forwardし、並行したV06実装・証跡・統合を保持した。

- Run18六契約はCOMPLETE。
- V06同期proofは`d446fc2f18f7a8603d1eedd446e93810dc44d01c`、evidence commitは`0880f6f30836873036b4d9908b7dcef50125d2c8`。
- 保存verificationは `verification/run18/runs/v06_alignment_20261115T152000Z_r01/verification.json`。statusはV06_ALIGNMENT_COMPLETE、289 checks／273 fixtures、10713 environment declarations、whole-project freshとbase public types preservedを記録する。
- 保存review decisionは`verification/run18/runs/v06_alignment_review_20261116_r01/decision.json`、scopeは五項目で、verdict PASS、Critical/Important/Minorは0、pending/declinedは空。これらは今回読み取った過去検証の記録であり、新しく実行した検証ではない。
- work統合receiptと独立結果は`verification/run18/runs/v06_alignment_integration_20261116_r01/`。元proof/evidenceを保ち、Run19準備文書の更新だけを例外として区別している。最新HEADと認証proof commitが同一だという表示をしない。
- 調査時の公開treeには`NSP14/NarrowFour/`、`NSP14/SmallEmbedding/`、`audit/run19/`、`scripts/verify_run19.py`、`docs/RUN19_CLOSURE_STATUS.json`を確認できなかった。`verification/run19/planning/`は原稿照合の記録であり、Run19数学の完了証跡ではない。別スレの未Push/実行中成果までは判定しない。

## 数学的主仕様と実入口

V06第6章§6.1–6.3、共通BRIDGE/CAP/MINCAP、依存・被覆、第5章N4、および旧registryのI_PARTITION/I_MAINを読んだ。全体SHAは`fe8271bbaabf6b3d31243628c3a5a5a305b82361c794f03c6e13a2fe98c72791`、第6章SHAは`67a10b00ab51ab1836fc071bb1c03b9fa2898ec470e84762151aeba032316f4d`。

実sourceとして以下を確認した。

- `Ordinary.ordinary_actual_completion_betti_le`：e≥3、w≥m−1、元k、完備接錐、双方自身の最小変数、全i。
- `NumericalSemigroup.narrow_width_comparison`：e≥5、物理狭幅、全i。
- `intervalCompletion`：現在の旧APIはhe≥2。全S targetはRun19の実API確認・literal carrier一致が必要。
- `carrier_totalBetti`と`completed_totalBetti`：同carrierでconductor witnessが異なる場合のactual transportに使える。
- `actualCutRank_two_le/le/triangular`、`degree_two_le_deficit`、`WidthNormalization`：実cutの条件と物理幅を供給する。
- Run15の`Run15Closed.all_original_goals_closed`は八つの元契約を閉じる。古いPARTIALレビュー文書だけから現在のordinaryを未完と判断しない。

## 採用した構成

主定理へ各枝の比較を引数として渡す条件付き統合、umbrellaへ型の表示だけ追加する方式、実productionの全域分割とtarget transportから無条件の公開定理を証明する方式を検討し、最後を採用する。ユーザーが求める全P14のLean化には無条件の全S/k/i出口が必要なため。

Run20の新担当はI_PARTITION/I_MAIN。Run19を推測で完了扱いせず、必要入力を実型・認証で確認してから合成する。原稿の全50 IDは実証明群とV06対応の最終台帳に用いるが、50個のwrapperを新設する要件にはしない。

重要な境界は、e=1の幅0、w=m−2/m−1、e=4/5、δ=0、source topとtarget topの相違、元kへの下降、d>1とm=d*u+2。<6,7,9,11>はsource e=4、literal targetは<6..11>でβ5=5なので、source消滅からtarget消滅を誤推論する検査に使う。

## 今回の変更範囲

成果物は[Run20指令書](../plans/2026-11-15-run20-v06-main-closure-order.md)と本設計範囲文書。既存数学source・原稿・検証器・証跡は編集しない。参照、担当ID、無条件主定理型、先行成果の現在/歴史区分、境界値、既存source不変を点検して通常Pushする。

実行スレで必要になるMain moduleやverifier/fixturesの作成は指令のTaskであり、この文書作成では行っていない。新しいLean build、公理probe、Run19/20数学の完成認証を行ったという表示をしない。
