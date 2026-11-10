# Run15 継続：intrinsic全変数Torと元体の全正行容量

基準aa98d3cf717b918e4c6c6b1d03bf59fb3ecfd70b。Run15全体は未完であり、この記録は実装済み接続の監査引継ぎ。

## 閉じた元の目標

HarmonicGoal、RelativeTerminalGoal、ActualTorToRowGoalに加え、CorrectedFullTransferGoalとOrdinaryBettiBoundGoalそのものを閉じた。後二つの追加仮定なしの証明はaudit/run15_fulltransfer/ClosedGoals.lean。元のRemainingGoals.leanは変更せず、productionはそれに依存しない。

環同値での通常Tor保存は、実projective resolutionのmapとtensor自然同型から証明する。同じcutのextended non-x basisとactual xを全最小表示に戻す実多項式環同値を構成し、augmentationを保つことを証明した。Z/x/lambdaの完全で重複しない実変数列をKoszul自由解消へ通し、native全変数複体のhomologyとintrinsic full totalBettiを一致させる。これにより前段のH0補正済み比較は元の全e変数に対する通常Bettiの不等式となる。

relative H0の実Zモデルからbeta0=f+1を得て、relative topと上次数消滅を保ち、全positive Euler行を既存数値上界へ通した。beta_j=c_j+c_(j-1)の正確な畳み込みとtarget差を使い、任意の元体・全i>=1でsourceのactual intrinsic Betti<=i*choose(m,i+1)を証明した。GのP/k有限性は仮定しない。原稿のordinary枝より強く、このsource数値容量には幅仮定が不要である。

## 残るもの

APBettiGoal、APConeBettiGoal、OrdinaryActualCompletionGoalの3目標は未完。一般d>=1のAP実公式・半群環と接錐のBetti一致、actual ordinary targetの通常Betti、literal完成接錐のactual targetとの全行比較を継続する。source数値容量をactual targetの公式と混同しない。第0行の双方1も後者の接続で保持する。

## 検証

scripts/verify_run15_fulltransfer.py --fresh-test-cache。空のproject test cacheから全受入を依存順で実行し、全新規宣言の通常/explicit型と全環境の許容公理、元の2つの目標のexact proof、旧原本不変、数値回帰を保存する。標数2の非自明shear、actual f=2の全変数比較、rank2/3の元体全正行を含む。実測原本はverification/run15_fulltransfer/verification.json。
