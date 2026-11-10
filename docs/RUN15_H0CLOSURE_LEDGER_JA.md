# Run15継続：actual H0作用と補正済みnative比較

基準20a449c8762bc38db17b48dcf14343a942ac880c。Run15全体の完了宣言ではない。過去原本を保持し、検証は新しいverification/run15_h0closureへ保存する。

## 証明済み

任意native ringの実要素列によるKoszulと、変数多項式環による既存Koszulの制限同型を構成した。同じactual x/lambda列のnative G-linear複体は既存のactual relative R-Koszulと実同型であり、通常のR-Tor、全Betti数、Euler値、必要な有限homologyに接続している。

実H0の境界はideal(x,lambda)であり、nativeToResidualの実kernelと一致する。native H0のG作用を実際のcomplement Zへ制限した加群がnativeCutH0Zである。nativeCutH0ZIsoは実Z加群同型であり、次元だけから作用を作っていない。全Z-Bettiは第0行1、正行i*choose(f+1,i+1)。

一般の実複体Kに対し、H0への実全射、実kernelの短完全列、kernel H0の消滅と正次数homologyの同型を構成した。実endomorphism coneの短完全列と有限homologyからdim boundを証明し、反復して実二項係数畳み込みを得た。この上界をkernelに適用して第0項を除外することで、補正済み有界比較correctedActionComparisonを証明した。chain groupの有限次元性は仮定しない。

ActualWitness.nativeFull_corrected_boundは同じactual R複体とZ作用を用い、上界を (T_(f+1))_i + binomialTransform_f(beta_R minus H0)_i へ接続する。H0補正は数値上の仮定ではなく実完全列に由来する。標数2の実H0非零Z作用と正Betti行、およびactual witnessへの一般適用をtests/NativeCutH0.leanで検査する。

また、環同値による制限とtensorの実線型同値・自然同型を構成した。これは後続の通常Tor保存の準備であり、それだけで通常Tor保存を証明したとはしない。

## 正確な未完

左辺のnative全変数複体を、元の全最小表示の通常Torへ同定する線型変数変換比較が残る。このため元のCorrectedFullTransferGoalは未完。同じactual R値を数値rowsに通しただけでintrinsic全行Bettiを閉じたとはしない。一般公差d>=1のAP実Bettiと半群環/接錐Betti一致、actual ordinary target、任意元体への最終下降、完成接錐の全行ordinary最終比較も未完。元の8目標のうち、HarmonicGoal、RelativeTerminalGoal、ActualTorToRowGoalの3つのみを閉鎖済みと数える。

## 監査入口

scripts/verify_run15_h0closure.py --fresh-test-cache。新規宣言の通常/explicit型、全環境の許容公理依存、空のproject test cacheでの全受入・旧数値回帰、基準commitからの既存数学/試験/監査/script/証拠不変を検査する。監査用のnative比較の型はaudit/run15_h0closure/ClosedGoals.leanに固定し、元のRemainingGoals.leanは変更しない。
