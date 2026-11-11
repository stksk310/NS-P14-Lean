# Run16 検証記録

最終判定は `final/verification.json` と `docs/RUN16_CLOSURE_STATUS.json`。`geometry/`・`transfer/`・`closure_checkpoint/`・`artin_checkpoint/` は同じrun内の途中受入であり、Run16完成の証拠をそれらだけから推測しない。

`red/` は未実装の受入口で失敗した受入型を保持する。検証対象の型を弱めてGREENにしたものではない。環境/producer未buildによる初期失敗は数学的反例と数えない。

`final_attempt_anonymous/` は、全146受入・数値回帰・公理抽出まで通過した後、匿名exampleをexport宣言として要求した集計assertionで止まった試行である。匿名exampleはLean環境に残らない。そこで同じ受入命題を名前付き定理に変更し、全モジュール・全新規宣言の通常/explicit型監査を維持して再実行した。対応表は `named_acceptance.json`。この旧試行には最終PASSラベルを付けない。

`final_attempt_named_scope/` は名前付き定理への移行時にsection仮定の明示includeが不足して止まった第二試行。意図した同じ仮定を明記して個別GREENを確認し、最終cold回帰を再実行した。production証明の不足ではない。

`coordinate_model.json` はactual最大分解長の動的計算と有限整数座標を独立に照合した799例。有限探索を一般証明へ置換しない。実際のPC/PG/Rとの一致はproductionの有限計算接続定理により別途証明し、三例九等式を任意体でLean受入している。

再現: 固定Lean/mathlibのcheckoutで `python3 scripts/verify_run16.py --fresh-test-cache`。生成oleanは現在のcheckoutの `.lake/build/lib/lean` へ書き、test fixtureのimportを依存順に解決する。過去原本はbaselineとbytes照合する。

最終独立レビューと対応は `final_review.json` および `docs/RUN16_FINAL_REVIEW_JA.md`（公開時に生成）。ZIPはsource/evidenceのSHA256とCRCを検査し、通常Push後にremote SHAを確認する。
