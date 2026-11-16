# Run20 入力棚卸し

採用base: `07fe1ed952ae31ce01255ce53df538bf0a76d5cc`。2026-11-16 JST、GitHub workを明示fetchし、Run19最終公開以降の追加修正なし。元の共有workspaceはRun17のclean checkoutで.git read-onlyのため触らず、`/tmp/ns-p14-run20-20261116` の `run20/implementation-20261116` へ独立clone（dissociate）した。旧Run19 source/HEAD/cacheは保持し、プロジェクトcacheはコピー、固定mathlib packagesだけを共有する。

Run19: proof `7c6821e`、evidence `c12fbfa`、review `1533762`、bundle `f92d484`、完了公開 `07fe1ed`。318 checks/299 fixtures/12792 declarations、48型監査module/2201型行/842private型行/28 named helpers。statusだけを根拠にせず、sources/input receiptで全source/evidence/review/ZIP Git bytesとhash、凍結10型、実production型・許容公理を再照合する。

実入口: SmallEmbedding.base_comparison / three_comparison、NarrowFour.narrow_four_comparison、NumericalSemigroup.narrow_width_comparison、Ordinary.ordinary_actual_completion_betti_le。targetは既存 intervalCompletionAll。旧intervalCompletionとはcarrier equalityからactual completed Bettiを運ぶ。e=1で全体構造を同一視しない。

原稿はV06全体・第6章・共通章・依存被覆。全体SHAと第6章SHAをreceiptで照合する。Run19の強いLTV線形上界／一般initial-ideal等式の非主張を保持し、必要比較の独立な直接証明を採用する。

I_PARTITION/I_MAINは本runで閉じるまで未完。Run18 COMPLETE/V06_ALIGNMENT_COMPLETE/Run19 COMPLETEと全P14完成を区別する。

実照合結果: `verification/run20/sources/adopted_run19_v06.json` はPASS。10出口と通常/explicit/展開型、公理はInputTypes記録に保存。Main追加後にも同checkerを再実行してPASSし、旧bytesの三つのappend-only prefixを保持している。I_PARTITION/I_MAINの新実証明とGREEN受入は本runの別成果であり、Run19証跡に後付けしない。

最終freeze前に最新workを再fetchし、到着監査 `342fbdda072fc5d6aa5e8f2d8968456cc54c12a6` をmergeした。数学Lean差分は0、公開ガード2scriptの補強と独立監査証拠394ファイル。元のpolicy/baseは書き換えず、このcommitの差分全件をexact Git bytesで許可・保持する追補とした。Run20にもreviewed-source差替えの実Git RED→GREENを追加し、最新Run19の35 controlsを同commitの隔離checkoutで継承する。追補一覧は `verification/run20/sources/arrived_run19_audit_20261116.json`。
