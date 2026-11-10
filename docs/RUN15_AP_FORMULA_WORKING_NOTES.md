# Run15 AP公式の継続中メモ（checkpointで停止しない）

最新公開HEADは88d6f3e77a3e4f50fe3589d3af7986144521ad39。元の8目標のうちAPBettiGoalだけが未完、他7目標はexact theoremで閉鎖。Run15全体PARTIALを維持し、AP公式を仮定fieldへ移さない。ユーザーは小区切りでの停止に不満、同じrunを続ける。過去の固定原本は変更しない。

## 今回のGREEN production（未コミット）

Homological: RankOneIncidence, VandermondeSpark, KoszulIncidence, KoszulMomentRank, RegularModuleReduction, BasisShiftWindow, CoefficientSlotsEquiv, FactorRange, TwoStepSlots, TwoStepBoundary。
ArithmeticSequence: OrdinaryModel, HeadIndex, ModelCoordinates, ModelMultiplication, ModelQuotient, ModelKernel, AtomIndices, ModelKernelShift, ModelNativeWindow, WindowArithmetic, ModelWindowAction。
合計21 module（最後の3 generic modulesを含む）。root importsはまだ追加していない。各moduleのlake buildは通過、tests/APResolutionFoundationsとtests/APKernelWindowの直接lean検査も通過した。全回帰/環境公理監査/ZIPは今回stageについてまだ。

- ordinaryModelは実Gamma=<v,...,2v−1>、v>=2。そのcarrier=0又は>=v、order=floor(n/v)。既存最大埋込次元cone Betti公式をそのまま使える。
- AP headの実基底Fin m、範囲外単項式0、積表を全添字で証明した。headIndexMonomial i*jはceil((i+j)/v)=ceil(i/v)+ceil(j/v)のとき添字i+j、その他0。
- modelExponent i=2*ceil(i/v)*v−iでordinary cone基底とNatをbijection、次数=ceil(i/v)。実coneの積表が同じになり、modelToHeadという本当の全射AlgHom B→actual Aを構成した。
- modelKernelはその実核。基底は添字>=m、modelKernelCoordinatesでtail Finsuppと同値。basis Nat nは絶対添字m+n。
- modelKernelXはactual x actionで基底n→n+v。actual regularityから単射。
- actual R-module quotient J/xJはmodelNativeQuotient。modelNativeWindowEquivでFin v→kと同値、有限性を実証明。modelKernelReductionIsoはactual Jのnative x-Koszulをこのactual quotientへ縮約、全remaining R作用を保持。JやBのk有限性は仮定しない。
- D=residueDefect=v−((m−1)%v)。window n<Dはlower、n>=Dはupper。modelWindowClass_twoStep: variable indexjはn<DかつD<=n+j<vのときwindow n+jへ、それ以外0。これがHankel作用の実証拠。
- KoszulMomentMapの符号はactual recursive KoszulSlotArrowから取得。Vandermondeで小部分集合独立性を証明し、p>=dで単射/p<=dで全射（cardσ+1=d+n）。仮想matrixのrankだけで終わらず、TwoStepBoundaryは実係数Koszul境界をsurjective lower projection→moment map→injective upper inclusionに分解し、実range finrankと同定した。

## /tmpでGREEN、production移行前

- /tmp/TwoStepBetti.lean、/tmp/twostepbetti.log（空）：actual polynomial module Mの係数同型e:coef M≃k^d×k^n、実変数作用がevaluation rank-one形であること、distinct points、d>=1、d+n=cardσ+1から全iの通常Bettiを計算。
  beta_i = if i+1<=d then(d−i)*choose(cardσ+1,i) else(i+1−d)*choose(cardσ+1,i+1)。beta0=dも実証明。P-finite Mは明示interface、k-finiteはeから構成。
- /tmp/EvaluationVariables.lean、/tmp/evalvariables.log（空）：index:σ≃Fin rとdistinct pointsから、basis columnがpoint_j^index_iであるactual GL equiv evaluationVariableEquivを構成。polynomialLinearEquiv_totalBettiへ接続できる。Fintype.linearCombinationのinjectivityから作り、charに制約なし。
- /tmp/TwoStepActual.leanはchar2 actual firstOrderModule k1 0へTwoStepBettiを適用する回帰を構築中。/tmp/twostepactual.logを確認して続ける。まだproduction testsへコピーしない。

/tmpには各productionのprototypeもあるが、今後変更する際はproductionと取り違えない。

## 残る実接続（全部同じRun15で続ける）

1. actual J/xJのwindowをlower reversed a=(D−1−n)とupper b=(n−D)に分け、Hankel action X_j c_a=d_(j−1−a)を実証明。現在のmodelWindowClass_twoStepから算術で導く。
2. 残り変数の実GL evaluation changeを行い、作用をu(t)*ell(t)へ分解。TwoStepBettiをactual quotientへ適用。無限同標数拡大L=InfiniteScalarField kで十分なdistinct pointsを取る。有限元体は最後actualG_totalBetti_baseChangeで戻し、APConeBettiGoalの既存証明で代数環へ移す。
3. actual J全変数Torのregular reduction、usual polynomial modulesへの接続、Bのfull minimal variablesとAPのNonX variablesのbijection/renameを証明。AtomIndicesのactual index equivalencesを使用。有限性はBのfull polynomial finite moduleとNoetherian submodule、又は実finite window generatorsから供給する。
4. actual short exact 0→J→B→A→0で、Tor(J)→Tor(B)が0をgradingから証明する。Jのminimum degree>=2、Bのpositive Torはdegree i+1に集中。これを未証明の退化/connecting消滅として仮定しない。generic graded regular reduction又はactual homogeneous projection B Koszul→B/x KoszulのquasiIsoからBの線型性を証明する候補。
5. real LESでbeta_i(A)=beta_i(B)+beta_(i−1)(J)、B公式i*choose(v,i+1)とquotientのTwoStepBettiからGSS profileを導く。beta0とtopも保持。v=1は既存twoGenerator_cone_bettiとsemigroup_cone_totalBettiで別に閉じる。D=v（upper dimension0）はgeneric TwoStepBetti自体が扱える。
6. frozen original APBettiGoalそのものをaudit theoremで閉じる。Task2のprofile lower bound/Fmin/width monotonicity、actual interval targetへのexport等も元の計画と照合し、8 goalsだけで全task完了と数えない。
7. 全verification、全環境型/公理、旧固定原本不変、原稿台帳、監査ZIP、normal Push、remote SHA/clean、Run15全体のfresh review、実測再校正。

## Lean上の注意

- coefficientKoszulComplexとcoefficientKoszulListFunctorのactual choicesをrwで混ぜると型が同じ見た目でも失敗する。core theoremは後者のfactoryに揃え、最後coefficientKoszulListFunctor_fullとcoefficientKoszulFunctor_objでcanonicalへ運ぶ。
- 係数restrictionのk actionと既存quotientのk actionはdefeqでない場合がある。modelNativeWindowIdentityでactual identity mapを構成し、map_smulでalgebraMap_smulを使った。
- module productのsumをfst/sndで見るとsimpだけでは降りない。TwoStepSlots.finiteSum_fst/sndはAddMonoidHomで証明済み。
- choose上段cardσ+1をhcardでd+nへ書き換えるとき、weighted choose/hD/hS/goalの全てを揃える。TwoStepBettiで対処済み。
- Nat.div/modのnlinarithは剰余非負/減算復元式を明示して渡す必要がある。same-name local hvで2<=v証明をshadowしない。

## APFOUNDATIONS全検証結果と次の研究原本

23module1802行、96 commands PASS、全5938/新規316宣言、旧1886ファイル不変、実測241.201秒。verification/run15_apfoundations。TwoStepBettiとEvaluationVariablesはproductionへ移行済み、tests/TwoStepActualも標数2の実moduleへ適用してGREEN。APKernelWindow/APResolutionFoundationsと合わせ3testsを通過。root imports/status/A69/A70/ledger/Scope監査/全検証を今回snapshotへ保存。通常Push後はこれらを固定原本にする。

検証中の/tmp研究：ReverseWindowSplit.leanはGREEN。WindowPolynomialModule.leanは最後のPi.basisFun_apply修正後GREENか/tmp/windowpoly.logを確認。actual quotientをP=k[X1,...,X_(v−1)]へ制限する実module、有限性、window/pair座標、実Fin v basis、変数作用の基礎。
HankelAction.leanはmap線型性のみ、Mathlib.Algebra.BigOperators.Ring.Finsetを明示importしてGREEN。HankelDelta.leanはhankel作用をwindow deltaへ評価する数式補題を構築中（Fintype.sum_eq_singleを供給するimportを追加する必要）。まだこれらを今回productionへ含めない。
