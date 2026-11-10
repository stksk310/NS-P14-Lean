# Run13 未完宣言と接続境界

基準Run12：`6b8d16889ea9b4d88567f0d9ac70391db2a49824`。指定Run13の完成条件は変更しない。
以下の名前は**必要な未実装exportの設計名**であり、Leanへaxiom/構造field/仮定として登録していない。

| 必要な宣言 | 正確に残る結論 | 供給済みの入力／残る証明 |
|---|---|---|
| `torKoszulIso_naturality` | 任意P加群写像f:M→Nについて、通常Torのfによる写像と既存koszulHomologyFunctor.map fがtorKoszulIsoを通して可換 | objectwise `torKoszulIso`、実Koszul functor、projective-resolution comparisonはある。tensorKoszulIsoのfに関する可換式が未証明 |
| `torBalancingIso` / `minimalResolutionBetti` | Mの実極小自由解消Qが与えられたとき、Qᵢの自由rankと既存totalBettiの一致 | 既存Torは第二因子kを解消。mathlibのTor'は第一因子を解消する別定義で、Torとのbalancingは同ライブラリでも未供給。二重複体又は同等のresolution比較が必要。極小解消の存在は使用も仮定もしていない |
| `gradedKoszulComplex` / `gradedBetti_total` | Kᵢの内部次数をMの次数+iで扱い、dが内部次数0、homologyの実直和分解・有限台、total=gradedの有限和 | 現在は次数を忘れたP加群複体。Mのgradingを恣意的に振るモデルを導入していない。実graded subquotient構成が必要 |
| `jumpStratum_gradedTor_shift` | Run12の同jump mapの内部次数差sをhomology/Tor上でも保持 | 元の実加群map `jumpStratumEquiv_degree` は証明済み。通常Tor・totalBetti保存は今回閉鎖。graded複体との接続は未完 |
| `koszul_shortExact` / `koszulConnecting` | 実加群短完全列を各Koszul次数の短完全列へ送り、実connecting mapと通常Tor比較を結ぶ | 任意短完全**複体**のconnecting/rank式は証明済み。koszulFunctorのcomponent mapがblock対角になる自然性と、各次数でのexactnessを実証明する必要がある |
| `partialEuler_syzygy` / `boundedFilteredComparison` | 部分交代和と実syzygy rank、rank0の非負性・末端、有限filtration/二重複体の必要な次元比較 | 正次数およびH₀の局所rank補正式はある。十分な有限自由解消又は証明済み代替との接続が未完。spectral sequenceの退化は仮定しない |
| `koszulPolynomialBaseChangeIso` / `totalBetti_baseChange` | f:k[Xσ]→L[Xσ]に沿う実拡大加群M_Lについて、L⊗ₖK(X;M)≅K(X;M_L)とβᵢ(M_L)=βᵢ(M) | L⊗ₖk[Xσ]≃L[Xσ]、実L⊗ₖ複体のhomology/有限性/次元保存は証明済み。P_L作用を持つ実加群との自然な複体同型が未証明。現在の`extendedCoefficientKoszul_finrank`をこの定理と読み替えない |
| `actualG_polynomialBaseChange` | actual G/T/A/N/Qと、係数をLに変えたactual対象との自然なP_L作用/核/商の整合 | Run12の指数基底・actual graded comparisonはある。形式級数環全体のtensor同型を使わずpiece/加群で接続する必要がある |
| `initialRank_blockComparison` | O_HARMONICで使う初項rank比較とblock三角化の一般橋 | 全ideal初項に基づく標準単項式の実商基底と±1 minorの任意標数非零性は閉鎖。特定sourceのinitial idealやharmonic本体は予定どおり後続担当 |

## 受入検査の不足

- 自由PのBetti=(1,0,…)、空変数列・上次数IsZero、実P/(X²)の通常Tor比較と有限性は検査した。
- **P/(X²)のBetti=(1,1)の数値同定、n変数残余体のbinomial Bettiは未証明・未検査**。
- 標数2の実Tor/全変数null-homotopy、標数2からRatFuncへの実複体scalar extensionを検査した。これは未完のP_L-Koszul/Betti保存の代用ではない。
- actual ℕ、二生成元、jump2と3を持つ半群、actual G/T/A/N/Q、同jump Tor/totalBettiを検査した。graded shiftのhomology検査は未完。

## 判定

今回の閉じたexportは監査・再利用できる。ただしRun13のTask1–8全達成、X_BASIC、I_FIELD閉鎖は主張できない。
障害は追加の公理ではなく、上表のresolution balancing・graded subquotient・changed-polynomial-module comparisonの形式証明をまだ構成できていないことである。
次の実行はRun13の継続としてこれらを埋める。予定run数に合わせて要求を縮めない。

## Universe interface

現在のTor/monoidal接続は `k σ : Type u` と `ModuleCat.{u}` を使う。
actual半群のTor/totalBetti運搬は `k : Type` のexportである。
表示・多項式有限生成・初期Koszul等のより一般のuniverseは型一覧で確認できる。
必要なら変数型のULiftとrenameによるuniverse transportも追加する。任意標数性を制限する仮定ではない。
