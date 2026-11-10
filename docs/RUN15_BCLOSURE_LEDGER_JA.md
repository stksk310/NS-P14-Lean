# Run15 継続：actual B・Tor資源行・残余Z作用

この継続記録はRun15全体の完了宣言ではない。基準は公開work ecbbf334479e1d91572cfd75914abaf8015d371e。過去の証明・試験・監査・検証原本・ZIPを保持する。

元の8命題中、HarmonicGoal、RelativeTerminalGoalに加え、ActualTorToRowGoalそのものを閉じた。証明はaudit/run15_bclosure/ClosedGoals.leanのactual_tor_to_row_closed。追加の比較結論や未証明の入力はない。productionから監査用命題への依存もない。

## 閉じた接続

1. actual B=A/highIdeal(2)の基底を構成し、長さeと独立なlambda作用を証明した。同じcutのhighIdeal(2)とX2の実同型、実短完全列0→X2→A→B→0からBのEuler値を既存TargetMargin.lowerへ接続した。
2. 既存actual x比較と同じtower/Hの資源行を合成し、全1≤j≤rでactual R-Torの部分交代和を既存資源rowへ上から評価した。ActualTorRow.actualTor_target_rowはさらにRun14 W.all_rowsを適用する。相対環はr+1変数であり、c_rの消滅を仮定していない。
3. Bを実代数として自明二乗零拡大へ同定し、同じextendedHeadBasisによりlambda-prefixと補完Zの全non-x作用を一致させた。cutBModelIsoは実P加群同型。
4. headToResidualの実kernelをcut idealと一致させ、actual A/(lambda)とk⊕k^fの実代数同型cutResidualEquivを構成した。補完Zは対応する独立な一次基底へ作用する。cutResidualModelIsoはこのZ作用を保つ実加群同型であり、通常のZ-Bettiは第0行1、全i≥1でi*choose(f+1,i+1)。f=0を含む。

## 正確な残り

actual R-Koszul H0と上記native商の同定を、同じZ作用を保って運ぶ必要がある。このnative商の同型だけではTask5は閉じない。全変数の線型変数変換による通常Tor保存、第0homology補正を保持した実有界比較、一般公差d≥1のAP Betti/環・接錐Betti一致、actual target、任意元体・全行ordinary最終定理も未完。元のRemainingGoals.leanを変更して完成条件を弱めていない。

## 検証入口

scripts/verify_run15_bclosure.py --fresh-test-cache、verification/run15_bclosure/verification.jsonが実測原本。空のproject test cacheから全受入を依存順で実行し、旧数値回帰、新規通常/explicit型、全環境の許容公理依存、ecbbf33基準の既存原本不変を検査する。標数2のactual rank2/3、B、f=2の非零Z作用とBetti、f=0の境界を受入に含める。
