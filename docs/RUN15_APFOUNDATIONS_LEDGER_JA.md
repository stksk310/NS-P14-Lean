# Run15 AP公式の実kernel・境界rank基盤

基準88d6f3e77a3e4f50fe3589d3af7986144521ad39。一般APBettiGoalは引き続き未完、元8目標のexact閉鎖数は7のまま。今回の基盤を一般AP公式の完成や別の入力fieldとして扱わない。同じRun15で継続。

23数学module。実ordinary補助cone Bからactual AP head Aへの全射、その実核J、Jのtail basis、actual x shift、正則縮約、実J/xJの有限windowと二次数作用を構成した。別途、actual Koszul signsを使うevaluation境界の最大rankと実二次数多項式加群の全Betti公式、実Vandermonde GL変数変換を証明した。詳細はRUN15_AP_FORMULA_WORKING_NOTES.md、原稿対応A69/A70。

受入は標数2で実B/A/J、非零lower→upper作用、upperの消滅、actual R-module quotientの有限性、native kernel正則縮約、critical signed blockの可逆性、実firstOrderModuleの全行Betti計算。三つの新testsで検査する。未証明のAP公式やTor写像消滅を受入前提へ置かない。

全回帰・通常/explicit型・全環境公理・旧固定原本不変・空test cacheはscripts/verify_run15_apfoundations.py --fresh-test-cacheで検証し、verification/run15_apfoundationsへ保存。監査audit/run15_apfoundations/Scope.leanは今回のactual kernel scopeを証明し、original APBettiGoalを閉じたとは主張しない。

残る主接続はactual window作用へのGL/rank公式適用、intrinsic通常Tor/最小変数の同定、gradingによるJ→BのTor写像0、実LESの合成と原体への下降。完成条件を弱めず進める。
