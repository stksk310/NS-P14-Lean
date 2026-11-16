# Run15 H0・実有界比較 継続メモ

ユーザーは未完での停止に不満。途中チェックポイント後も同じrunを続ける。通常Pushは包括許可済み。Run15全体は未完であり完成フラグを変えない。

## 公開チェックポイント

20a449c8762bc38db17b48dcf14343a942ac880c = origin/work（照合済み）。actual Bと元のActualTorToRowGoalを閉じた20module1168行。verification/run15_bclosureは81コマンドPASS、全4942/新規306宣言、公理は許容3種のみ、旧1311ファイル不変、実測204.157秒。監査ZIP SHA1818fa11bb3e02a0a5cf88eeae37de7769c5b7f0e4dd31041621b27d7e1be6fb。過去証拠・数学・試験・監査・scriptをこれ以降変更しない。新たな全検証はrun15_h0closure/base20a449cで作る。

## 現在の未commit数学

- ActionKoszul: 任意CommRingの実要素列からnative R-linear Koszul functor。restrictionと実同型、通常のpolynomial variable complexとの実同型。
- ActionKoszulH0 / ActionH0Ideal: native complexの実boundary、native H0≃R/ideal(rs)、R-linear。actionRegularComplexがregular native Kを抽象Rの時点で固定するfactory。
- ActionH0Image: native H0を実surjectionのimageへR-linear同定。actionRestrictedH0はそのH0を別の実polynomial actionへrestrictするmodulefactory。actionRestrictedH0Isoは作用を保持する。
- NativeCutH0: 同じcutのnative x/lambda列、実ideal、headへの像=cutIdeal、nativeToResidualのkernel=実ideal、actual native G-H0の商同定。GREENだがfactory修正後再buildを確認する。
- NativeCutH0Z: native H0の実G作用をcomplement Zへrestrictし、nativeCutH0ZIsoでfirstOrderModelへ実Z同型。全Z-Betti行を証明。factory修正前GREEN。
- ActionCoefficient: native Kのcoefficient restrictionと通常polynomial Koszulの実同型。
- RelativeNativeKoszul: 同じnative x/lambda Kと既存actual relative R-Koszulの実複体同型。nativeRelativeEuler、nativeRelativeBetti、nativeRelativeHomology_finiteはGREEN（factory修正後再確認）。Gのk/P有限性を使わない。
- H0Truncation: 任意native complex K→single0 H0の実全射、H0準同型、kernelの実短完全列。
- H0KernelHomology: kernelのH0=0、全positive H=KのHの実同型。GREEN。
- EndomorphismConeBound: 任意の実endomorphismのconeから実短完全列、有限homologyの伝播とdim cone_i≤dim K_i+dim K_(i−1)。chain finite不要。GREEN。
- NativeCoefficientComplex: native ring→kの複体・H比較、正確性保持、H0kernelのfinite、native scalar coneの実有限性/上界。GREEN。
- ActionOnComplex: complexに実scalar coneを繰返すfunctor、single0との同型、実短完全列を保存。GREEN。
- PascalBound: 実coneの反復上界のPascal反復とbinomialTransform（choose畳み込み）の等式。GREEN。
- ActionComplexBound: 有限なのはhomologyだけで、反復coneの実二項上界。GREEN。
- CorrectedActionComparison: K→single0 H0のkernelに上界を適用し、実短完全列からH0補正を残す一般有界比較。第0homologyを粗いchain数で置換しない。GREEN。
- ActionSingleCoefficient: H0へのZ Koszulが実Z-module通常Koszulを計算するgeneric helper。
- NativeFullTransfer: 一般の補正済み比較を同じactual Wへ適用中。現在build /tmp/nativefull.log。nativeH0ComplementComplex全体をabstract ringで固定するhelperfactoryを入れ、具体G上のlimit dataのdefeq timeoutを避ける修正中。**まだGREENとはしない**。
- tests/NativeCutH0.leanは用意済み、まだcompileしていない。
- rootにこの段の新規modulesは未append。全回帰/台帳/status/ZIP/Pushもまだ。

## 残る大きな数学

1. NativeFullTransferを実actual Wで閉じる。現在のnative full complexのhomologyとintrinsic full Torとの変数変換比較は別。
2. 全最小表示の線型変数変換で通常Tor/Bettiが保存される実証明。
3. native補正済み比較を既存R rowsとtarget差へ通す。
4. actual ordinary targetと一般d>=1 AP Betti/半群環・接錐Betti一致。
5. 任意元体・完成接錐・全行ordinary最終export。元の8goalのうち閉じたのはHarmonicGoal/RelativeTerminalGoal/ActualTorToRowGoalの3個。まだ他を閉じたと報告しない。

## 次のGL/Tor保存の具体案（未証明）

任意ring equivalence e:R≃Sに対しModuleCat.restrictScalars eがカテゴリ同値。
mathlibにFunctor.mapProjectiveResolutionがある（CategoryTheory/Preadditive/Projective/Resolution.lean）。
PreservesProjectiveObjectsはIsEquivalenceからinstance済み。
標準Koszul resolutionをeでmapし、TensorProduct.congrのsemilinear identity equivを使い
F(M) tensor_R F(N)≃F(M tensor_S N)を実自然同型として構成できる。
この同型とhomology comparisonで通常Torの同値を証明し、augmentation-preserving polynomial AlgEquivに適用する経路。
TensorProduct.congrはLinearAlgebra/TensorProduct/Map.lean:263、同一のsemilinear mapによるtensor上の同値。可逆ringhom pair instanceを使う。
単にAlgEquivを作っただけではTor保存としない。

## Lean要注意

計算されたnative Gのhomology/limitを複数の式で再構成すると、同じ見た目でもModuleCatのchoice dataのdefeqで20万HBのwhnf timeoutが出る。HBを増やすより、**abstract Rの時点で複体全体を固定するfactory**を用意し、concrete actual consumerは同じfactoryにdelegateする。C.nativeCutComplexとactionRestrictedH0の双方がactionRegularComplexを使うよう直近修正した。
小さなdefをunfoldしてから大きなfunctor/complexをapplyすると安定する。mapHomologyIsoの型はlet e:K.homology i≅J.homology iと明示し、functor.objのまま推論させない。TCで∀i ModuleFiniteが見つからない場合、opaqueなcoefficient wrapperとFunctor.objの違いを正規化し、実証明を局所instanceとして具体的に与える。
Mathlib.Tactic全体をimportしない（未cacheの大規模buildが走る）。PascalBoundはMathlib.Tactic.Ringのみに変更済み。無関係の依存バージョン変更なし。

## その後の確定結果（上の「途中」記載よりこちらが最新）

NativeFullTransferを含む21 production module・1213行が全てGREEN。tests/NativeCutH0.lean、audit/run15_h0closure/ClosedGoals.leanも含め空project test cacheから全83コマンドPASS。全5249宣言/新規307宣言、許容公理のみ。verification/run15_h0closureに保存済み。root21import追加済み、statusと原稿A61/A62・H0CLOSURE_LEDGER更新済み。この段はまだRun15完了ではない。

NativeFullTransferの最終exportはActualWitness.nativeFull_corrected_bound。左辺はW.cut.nativeExtendedCoefficientComplex.homology i、右辺はif i=0 then1 else i choose(f+1,i+1) + binomialTransform f (beta_R with zero H0) i。actual witnessへ追加仮定なしに適用済み。all R Betti inputはnativeRelativeHomologyIso / nativeRelativeBettiにより既存通常R-Torと一致する。H0モデルの全Z作用もnativeCutH0ZIsoで一致する。

重要なfactoryの最終形：
- actionRegularComplex R rs、actionRestrictedH0 rs phi。
- actionH0SingleCoefficientComplex k R sigma rs phi xs。
- regularPartialCoefficientComplex k R rs、regularExtendedCoefficientComplex k R sigma rs phi xs。
- 実有界比較をabstract Rで固定したregularCorrectedComparison。
- C.nativeCoefficientCutComplex / C.nativeH0ComplementComplex / C.nativeExtendedCoefficientComplexはこれらのabbrev。W.relativeRegularGIsoはregularModuleのactual relative Gへのidentity同型。
- nativeH0ComplementIsoは結果型を推論させると安定。actual concrete GでhomologyMapIsoの型を再elaborateするとまだtimeoutするため、abstract RのactionH0Canonical_finite / actionH0Canonical_bettiを実証明で用意し、それを適用して閉じた。HB増加で済ませていない。

## 次のGL/Tor proofは/tmpで既にGREEN（まだproductionへ入れていない）

1. /tmp/RingEquivTor.lean：ringEquivTorIso。通常mathlib Tor_R(FM,FN)≅F(Tor_S(M,N))。F=restring equivalence。実ProjectiveResolution PをF.mapProjectiveResolutionし、既存RingEquivTensor.restrictTensorNatIsoをcomplexへ運び、homology preservationとisoLeftDerivedObjで閉じた。全一般CommRingR/S、M/Nに有限性仮定なし。
2. /tmp/PolynomialEquivBetti.lean（public import RingEquivTor）：augmentation-preserving polynomial AlgEquivのresidueField実同型、polynomialEquivBettiIso、有限生成の実伝播、通常totalBetti保存。GREEN。polynomialEquiv_totalBettiはinclude he in、finite lemmaはFintype仮定をomitしてlinterclean。
3. /tmp/LinearVariableBetti.lean（public import PolynomialEquivBetti）：linearPolynomialのaugmentation0、polynomialLinearEquiv_augmentation、polynomialLinearEquiv_totalBetti。GREEN。
これらの/tmp .oleanも--root=/tmpで作った（LinearVariableBettiはまだolean未作成）。/tmp importの実験はLEAN_PATH=/tmp PATH=/tmp/ns-p14-lean/bin:$PATH lake env leanを使用。production追加時はimportをNSP14.Homological.RingEquivTor等へ直す。次の全検証は今回のPush後SHAをbaseに別dir（run15_fulltransfer等）を作る。この段の21math/tests/audit/scripts/evidenceは一度Pushしたら不変に保つ。

これらをproductionへ追加し、same-cutのactual full linear variable changeへ適用する。AtomExponent≃Option NonXAtomはまだ無い。LinearEquiv.piOptionEquivProd k、prodCongr(refl,C.extendedCoefficientEquiv)、LinearEquiv.funCongrLeft k kでfull coefficient equivalenceを作る経路。full polynomial変換にnone=xとsome=同じextended非x basisを保持することを証明し、native full complex→通常Torへ同定する。AlgEquivだけでTor保存としない問題は、上のGREENなgeneric Tor証明で解決できる見込み。
