# Run15 full-transfer継続メモ（停止しない）

ユーザーは未完での停止に明確に不満。Run15は同じrunで続ける。通常Pushは包括許可済み。完成条件を弱めない。原稿・台帳・各チェックポイントの原本を保持する。

## 最新の検証範囲

基準aa98d3cf717b918e4c6c6b1d03bf59fb3ecfd70b。今回16新規数学module696行、2新規tests、audit/run15_fulltransfer/ClosedGoals.lean。空project test cacheから全86コマンドPASS。全5366/新規117宣言、許容公理propext/Classical.choice/Quot.soundのみ。旧1542ファイル不変。実測194.391秒。verification/run15_fulltransferに型・公理・全ログとhash保存済み。root追加・status・原稿A63–65・ledger更新済み。通常Pushはこれから行う。

元の8命題のうち閉じたものは5：HarmonicGoal、RelativeTerminalGoal、ActualTorToRowGoal、CorrectedFullTransferGoal、OrdinaryBettiBoundGoal。今回後ろ2つを元の宣言のままauditで証明した。まだAPBettiGoal、APConeBettiGoal、OrdinaryActualCompletionGoalが残るのでRun15 COMPLETEではない。

## 今回のGREEN production

- RingEquivTor.ringEquivTorIso：実mapped projective resolutionとtensor自然同型による通常Torの環同値保存（任意modules、有限性仮定なし）。
- PolynomialEquivBetti：augmentation-preserving AlgEquivのresidue module実同型、通常Tor/Betti同型、実有限生成伝播、totalBetti保存。
- LinearVariableBetti：linearSubstitutionのaugmentation0と通常Betti保存。
- OptionPolynomialEquiv：non-x polynomial AlgEquivをnone=xを固定してoption全変数へ拡張。PolynomialAugmentationはrenameのaugmentation自然性。
- Semigroup.AtomSplit：Option NonXAtom≃actual AtomExponent。
- FullVariableChange：同じC.extendedPolynomialEquivをactual xと合わせた全最小表示の実AlgEquiv。none/someの実像、augmentation、extendedFullToG。
- FullVariableBetti：新全変数作用の実module、元のminimal moduleとの制限同型、全変数通常Betti保存。
- FullVariableOrder：Z++x++lambdaのactual全変数順、完全/重複なし、全変数作用の一致。
- ActionAppend：反復native scalar coneのappend実複体同型、通常full-list自由Koszul解消を使う実Betti同定。
- IntrinsicFullTransfer：nativeExtended_intrinsic_betti、W.correctedFullTransfer_nat/Q。元のCorrectedFullTransferGoalそのものを証明済み。
- RegularH0Dimension：native partial H0と実Z-moduleの係数同型からlength=f+1を計算。
- RelativeRowsAll：actual relative beta0=f+1、j>=r+1のEuler0、既存target rowを全positive jへ（target余剰非負を保持）。
- BettiEulerConvolution：beta_j=c_j+c_(j-1)の正確な有限畳み込み、zeroth補正を明示。
- NumericalBettiClosure：W.ordinary_betti_bound_extension、Ordinary.ordinary_betti_bound。任意元体、e>=3、全i>=1でactual intrinsic source Betti<=i choose(m,i+1)。この数値capacity上界には幅条件不要（原稿より強い十分な結論）。体拡大はactualG_totalBetti_baseChangeで元のkへ戻した。targetの実公式とは混同しない。

## 残りの主作業

1. actual ordinary targetのBetti公式、第0行を含むliteral completion比較（OrdinaryActualCompletionGoal）。
2. 一般d>=1のAP実Betti公式（APBettiGoal）。
3. 一般APの代数半群環/接錐Betti一致（APConeBettiGoal）。
まだRun15全体を完了としない。一般APをd=1へ縮めない。

## 次のactual target向け準備（/tmp、まだproductionに含めていない）

/tmp/MonicCone.lean：GREEN、/tmp/MonicCone.olean作成済み。
- acyclicKernelHomologyIso：実short exact complexesのkernelがacyclicならmiddle/quotientのhomology実同型。
- monicConeHomologyIso：実short exact complex A→B→Cでcone(A→B)のhomology≅Cのhomology。∞ chainも可、有限性不要。

/tmp/NativeKoszulExact.lean：最後の修正後GREENか/tmp/nativekoszulexact.logを確認。
- 任意CommRing RのactionKoszulFunctorのAdditive/Linear R/shortExact。
- actionCoefficientFunctor、実shortExact保存。
- actionCoefficientConsIso：r::rsのnative coefficient complexと、実module scalar rをfunctorへ通したconeの同型。
最後にFunctor.map_idが標準dataFunctorのmap_idと名前衝突したので、(actionKoszulFunctor R rs).map_id Mへ明示修正。--root=/tmpでoleanを作成するコマンドが走った。Mathlib依存変更なし。

この2つを使い、native R=G、r=actual x regularの場合にK(x,nonx;G)≃K(nonx;A)のhomology同型を作る予定。APのxMultiply_injectiveは既存ArithmeticSequence/ConeRegular.leanで任意d/任意体に対してGREEN。
実short exact R --r→ R → R/(r)をgenericに構成し、actionCoefficientFunctorで送ってmonicConeHomologyIsoに入れる。source full complexはAtomSplitを使うactual AtomExponentの順x::nonX（完全/重複なし）とregularPartialPolynomialIso/fullList_totalBettiで通常Torへ接続できる。cutは不要なのでe=2 targetにも適用可能。

ordinary targetのAは全head order<=1からhighIdeal2=0を示す。head_iff_apery、AP Apéry formula、v=m−1を使う。全non-x variableのrank-one actionとindependent images、length=eをSquareZeroEulerの実rank定理に適用すると通常Betti=i choose(m,i+1)が計算できる。FirstOrderBettiのspecial Fin証明をgeneric Fintype moduleへ移植する経路（実rank証明を既に持つ）。

一般AP Bettiの未証明研究候補：kill X_vで残るHankel2次数moduleのKoszul boundaryが最大rankとなる±1 minorを作る。単なるlex/monomial初項Betti一致は誤り：m5,v3のactual Gorenstein headはBetti(1,5,5,1)、自然な初項moduleは(1,5,6,2)でcancellationがある。初項だけで一般AP式を断定しない。

## Lean運用

一度に一つのlake build。Mathlib.Tactic全体をimportせず必要なtacticのみ。raw actual G上でcofiber/homology limit dataを別経路再計算するとdefeq timeoutになる。abstract R factoryを共通に使い、actual consumerには同じfactoryを渡す。今回のfactoryとBetti helperはこの問題を解消してGREEN。旧math/tests/audit/script/evidenceはPush後不変、次検証は今回のPush SHAから新dirに作る。
