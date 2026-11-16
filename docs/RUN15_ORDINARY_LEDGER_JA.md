# Run15 ordinary actual枝の閉鎖（一般AP共通入力は継続）

基準86361155a028cc9a6d6134218c67600770075e1f。元の8目標のうちOrdinaryActualCompletionGoalを追加で閉じ、6目標がexact theoremとして閉鎖済み。監査型はaudit/run15_ordinary/ClosedGoals.lean。Run15全体は未完で、APBettiGoalとAPConeBettiGoalが残る。

実正則元の短完全列、単射の実写像錐と商のhomology同型により、x正則なactual Gの全変数Torをactual Aの非x Torへ縮約した。最大埋込次元AP v=m−1のApéryリストからAが実際にfirst-order square-zeroとなることを証明し、実boundary rankから通常Bettiを全行計算した。公差d>=1を保持するこの特殊族をliteral ordinary interval targetへ適用し、actual完成接錐の比較まで接続する。一般AP全体の公式とは別である。

actual sourceの第0Betti=1は、実多項式表示と実augmentationの全射、実Koszul H0の右完全性、free P/residue moduleの第0行から証明した。これは任意sourceに適用でき、Gのk有限性を仮定しない。完成source/target双方の第0行を等式で保持し、ordinary実比較は任意元体・全行・各自の最小変数を持つ。

検証入口はscripts/verify_run15_ordinary.py --fresh-test-cache。通常/explicit型、全宣言の許容公理、過去原本不変、空test cacheでの全受入、旧数値回帰をverification/run15_ordinaryへ保存する。rank2実sourceとliteral target、terminal26/41のchanging-jump source、標数2、二変数ordinary target、d=2のv=1/v=m−1 AP coneケースを含む。

未完の一般AP共通入力をconstructor fieldや公刊定理名axiomに置かず、d=1や最大埋込次元に縮めて完成扱いしない。引き続き同じRun15内で実証明を構築する。
