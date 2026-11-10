# Run15 B/資源row 継続メモ（runを終了しない）

公開済み途中基準: ecbbf334479e1d91572cfd75914abaf8015d371e = origin/work。
前段0604586から35 module・2,044行を追加し、77コマンド、全4,636宣言（新規441）、過去1,186ファイル不変を検査しPush済み。検証はverification/run15_xclosure、ZIPはartifacts/NS_P14_LEAN_RUN15_XCLOSURE_PARTIAL_20261110.zip（SHA 8a19badfcf4566249f53bcb51c9bcf8749c20e9a3ad455bbed48b6e3c4a19032）。これらを上書きしない。新たな全検証は別dir run15_bclosure、base ecbbf33で作る。

以下はその後の未commit作業。ユーザーは途中終了に不満。Run15の完成条件は弱めず、未完目標を解き続ける。

## GREEN production / exact goal

- HeadFirstOrderCoordinates: actual B=A/highIdeal(2)、低次数headの基底、Option(nonXAtom)との実同値、dim B=e。
- CutFirstOrder: 同じP作用のcutB、実完全列0→headHigh→A→B→0、有限性、λ作用。
- HeadConstant / HeadLinearTruncation: actual定数射影、次数1射影とBへの降下。各λが定数射影を通ることを実商で証明。
- CutBEuler: actual Bのλ像の独立性とrank-one actionをSquareZeroEulerへ適用し、c_j(B)=e*choose(r−1,j)−choose(r,j+1)、既存TargetMargin.lowerと完全一致。
- CutHighTwo: F_1=0から同じcutのheadHigh≅X_2。Eulerも同一。
- ActualLayersField: 同じHのfield independence。別cutの上界を選んではいない。
- ActualTorRow.actualTor_resource_row: 実第1x比較、B完全列、同じtower行を接続。元のActualTorToRowGoalそのものをaudit/run15_bclosure/ClosedGoals.leanで追加仮定なしに証明しコンパイル済み。
- ActualTorRow.actualTor_target_row: 既存Run14 W.all_rowsにactual R Tor値を通した。
- tests/ActualTorRow.lean（rank2/3、標数2）、tests/HeadFirstOrder.leanとも直接LeanでPASS。rootへ新規moduleはまだ未追加。
- HeadFirstOrderSplit: B≃k×A_1、actual平方零積。
- HeadFirstOrderAlgebra: B≃ₐ[k]TrivSqZeroExt k(NonXAtom→k)。実積を保持。
- Homological.TrivSqZeroCoordinates: Pi座標の線型同値が平方零拡大の代数同値を誘導。
- CutBModel: 同じextendedHeadBasisを使うnative Bの代数座標、λ-prefix保存、actual P-module cutBModelIso≅firstOrderModule(k,r,f)。余分なf=e−r−1生成元を保持。
- CutBFullAction: extendedPolynomialEquiv_X（全prefix/complement）、extendedPolynomialToB_model。全non-x変数、Zも含めてactual作用を一致させた。
- FirstOrderAction: firstOrderPolynomial_X のtyped補助。
- FirstOrderResidual: complementary座標への代数射、prefixλは0、complementZはunit vector、surjective。
- CutResidualAlgebra: headToResidual:A→Triv(k,Fin f→k)、fst/sndの実座標、highIdeal2≤cutIdeal、kernel=cutIdeal、actual cutResidualEquiv:A/(λ)≃ₐ[k]Triv(k,k^f)。直近buildを確認すること（最後の修正はproj1とheadLinearPart.valの定義的同一視を明示した）。

## 次

1. CutResidualAlgebra buildを確認。
2. cutResidualEquiv_mk と complementPolynomialToA（extended basisのZ部分）を作り、A/(λ)上の実Z作用がfirstOrderPolynomial(k,f,0)であることを代数準同型の等式として閉じる。
3. これをactual R Koszul H0へ自然性込みで運ぶ。単なるdim H0=f+1ではTask5未完。
4. 補正済み全変数Tor比較、actual ordinary target、一般AP実Betti/ring-cone一致、元の任意体全行ordinary閉鎖は未完。
5. 数値部を再実装しない。General AP d≥1は明示的義務なのでtarget d=1だけでRun15完成にしない。

## 有力な実装経路（まだ証明済みとはしない）

- 任意CommRing RとList Rに対するactionKoszulFunctorをscalarConeFunctorとsingle0から構成すると、G加群としてx/λ/Z作用を保持できる。ring homでの制限と写像錐の自然同型により既存R-variable Koszulへ接続できる。Gのk/P有限性は不要。
- 全e変数の線型変数変換Tor保存がまだ必要。旧CutBasisのextendedCoefficientEquivとatom≃Option(nonXAtom)からfull polynomial AlgEquivを作れるが、AlgEquiv構成だけをTor保存と報告しない。
- H0補正済み比較は実複体K→H0(K)[0]の全射とkernel K'（H0=0、H_i(K')=H_i(K), i≥1）を使い、Z-Koszulをかけて短完全列とcoarse二項係数上界を組み合わせる経路が有望。H0側のZ作用を上の平方零拡大モデルで正確に計算する。
- 一般AP Bettiの研究候補: AP cone/(x)の実Apéry基底0..m−1にX_vがv-stepで作用。coker(X_v)はdimension vのordinary平方零モデル、ker(X_v)はv個の末端基底を持つHankel型2次数加群。m=av+b, D=v−b+1でlower D, upper v−D、X_j c_a=d_(j−a)（範囲内）。そのKoszul境界がp≤Dで全射、p≥Dで単射（p=Dは±1 minor）なら必要なBetti数を計算できそう。ただしこれは未証明。x_vの二段homologyの高次connecting補正が0であることも別途必要。数値実験を証明扱いしない。

## Leanの落とし穴

- rwが見た目同じ式を見つけない場合、semireducibleな型同義語（TrivSqZeroExt=Prod、quotient/module carriers）がchangeで展開され、implicit transparencyでtype-correctと判定されなくなる場合がある。erw、fully applied lemma、typed helper、calc+exactを使う。実際CutBFullActionはRWfirstOrderPolynomial_Xで失敗し、typed calc+exactで13秒以内に閉じた。
- zero_smulのscalar型は明示すると安定：zero_smul k (1:S.HeadAlgebra k)。mul_oneも具体的な値を渡す。
- local let F/D（computed functor）のaliasはunifierを大幅に遅くすることがある。型を正規化してから使うかaliasを除く。
- 関係a∈Submoduleのconv_lhsはelementではなくSubmoduleを選ぶ。単純なrwや明示した位置を使う。
- doc commentはinclude ... in の後。
- 一度に一つのlake build。ログは/tmp。Lean4.36.0-rc2とmathlib pinを変更しない。

## 追加でGREENになったもの

- CutResidualAction: actual Z polynomial maps、headToResidual_Z_action、cutResidual_Z_action。
- RegularRestriction: polynomialRegularModule と一般の作用を保つ代数同値→加群同型。
- FirstOrderBetti: actual boundary ranksから全通常Betti、第0行1+f、extra=0でi*choose(r+1,i+1)。
- CutResidualModule: actual cutResidualModelIso、finite、length1+f、Z Betti第0行1/正行i*choose(f+1,i+1)。
- tests/CutResidual: intervalData5,4でrank2/f2、標数2のactual非零Z作用、Betti1=3/2=2、実rank2別例でf0を検査。直接Lean PASS、linter修正後は全検証へ。
- rootは新規20moduleをappend済み。scripts/verify_run15_bclosure.py --fresh-test-cacheを新規verification/run15_bclosureへ実行中、base ecbbf33。元の証拠は上書きしていない。docsstatus・ledger・原稿A59/A60更新済み。

## より直接の次の経路

/tmp/ActionKoszul.leanで、任意CommRing Rの実要素列によるactionKoszulFunctorをscalarConeFunctorの反復として構成中。restrictionと複体の実同型、既存変数Koszulとの比較は短い帰納法で通る見込み。native R=GでK(x,lambda;G)を作れば、G作用を複体全体・H0に保持できる。native H0≃G/ideal(x,lambda)はR=Gのregular moduleに対する実boundary rangeで証明し、actual head→cutResidualの商へ運ぶ。既存relative polynomial complexとの同型はrestriction比較で与える。この方法ではGのk/P有限性は不要。全変数への補正にはなおnative複体のgood truncation/有界比較が必要。
