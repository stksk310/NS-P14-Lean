# Run19 / Run20 引継ぎ

Run19の数学出口はNSP14.Run19のdistance_closed/words_closed/high_closed/first_closed/small_closed/width4_closed/narrow_four_closed/base_closed/ltv_closed/three_closed。受入型はaudit/run19/RequestedGoals.leanと10 acceptanceに実装前から凍結した。

Run20はN_CLOSE、I_BASE、I_THREEをRun18 narrow_width_comparison、既存ordinary全域出口と合成し、I_PARTITION/I_MAINを閉じる。e1の幅0にはS.intervalCompletionAllを使い、e≥2で既存completionとのcarrier同一性を使える。Run19に全P14の完成を含めない。

原稿との差分はRUN19_PAPER_CORRESPONDENCE_JA.md。特に幅4は直接actual kernel表示、三生成元は一変数端点による必要比較の独立証明であり、未証明のinitial-ideal/LTV線形上界を輸入しない。

検証はscripts/verify_run19.py --fresh-test-cache --output-dir verification/run19/runs/<new-id>。全289既存check/273 fixtureに新fixture/受入/モデル/経路/negative controlsを加え、全project lib/IRをfresh再構築する。mathlibの固定cacheは保持する。古いverification/artifactは不変。

このsource snapshotの閉鎖台帳は数学と公開の段階を区別する。最終の検証・独立レビュー・ZIP・通常Pushの実測値はverification/run19の新しいverification.json、review receipt、completion/publication receiptに保存する。それらが揃うまでRUN19_COMPLETEとは判定しない。ZIPは監査bundleであり完全offline checkoutとは呼ばない。
