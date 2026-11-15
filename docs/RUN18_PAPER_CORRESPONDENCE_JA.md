# Run18 原稿対応（PARTIAL）

Run18全体は未完である。現時点で閉じた担当IDは **W_SPARSE・W_FIVE** の二つ。残るX_BHP_EK・W_EDGE・W_DENSE・W_CLOSEを完了扱いしない。以下の11月13日/第1継続時点の記録は履歴として残し、最新の証明経路を末尾に示す。

## W_SPARSE：V03 V.3 / V02 §13.4 W17–W21

1. `Width/Progression` は任意の正ステップの正部分等差和を、任意の十分長いcutoffで正確に評価する。分母を払った等式をNatで証明する。
2. `Width/SparseVolume` はRun17の同じDの `wordVolume_growth_bound` から `(q+1)*W≤u²` を導く。余り付き恒等式の非負多項式を用い、素数位数や個々のoffsetのunit性を追加しない。
3. `Width/SparseRemainder` はe=6,7,8,9のB*に対応する `6W+u≤u²+12`、`6W+3u≤u²+20`、`8W+2u≤u²+25`、`8W+4u≤u²+36` を導く。幅の有限表ではなく、任意uのEuclid余りの3/4場合だけを分けた全称証明。
4. `Width/FirstResources` はactual QCの第三/第四調和上界と、同じ元のGの端点socle Rを、`actual_core_endpoint_bound` 経由で合成する。P_C=P_GやR=0を仮定しない。有理重みはQで扱い、係数体内の除法にしない。
5. `Width/SparseFirstSmall` と `SparseFirstLarge` は全e≥6の第一行を閉じる。大e側は原稿のz多項式、e=6..9は余り補正を使う。`SparseFirst` は元のSから幅V=d*uのliteral completionへ戻す。
6. `Width/SparseSecond` は第二行の支払い。e=6は原稿どおりの因子 `(u−10)(u−3)(u+1)`。e≥7は原稿のe=7/e≥8分岐を一つにまとめ、e=7+v,u=2e−2+zで `2u²−(3e+6)u+6e−2 = 2v²+5vz+12v+2z²+21z+4≥0` を使う。結論と範囲は同じ。
7. `Width/NormalizedCapacity` は原稿T_iを二項係数比による正規化容量として定義する。幅eの基点 `e−1+i/e`、各幅増分、隣接行での比の非減少を実証明し、全2≤i≤eでT₂≤T_iを導く。e−iで割らないためi=eも含む。
8. `Width/SparseHigher` はactual Gの加法形資源不等式を経由し、全2≤i≤eで `β_i≤i*C(u,i+1)`。`SparseComparison` はi=0の両辺1、i=1、2≤i≤e、i>eを合成し、各環自身のactual最小変数列で元の完備接錐を実targetと比較する。
9. `audit/run18/PartialClosedGoals.lean` の `NSP14.Run18.sparse_closed` が凍結された `Requested.W_SPARSE` を追加前提なしで閉じる。体・source・正規化・d・mは同じ。u<mだけの広いEHへ最終比較のscopeを拡張していない。

## 基礎整備であり閉鎖に数えない部分

`Lex/Ideal` は一つの実lex ideal、実極小生成元、一般斉次商のgraded Betti/Hilbertを定義する。`Lex/Hilbert` は全商がArtinでなくても次数pieceが有限次元であることを証明し、既存のactual graded/total Tor同一性へ接続する。これらはBHP/Pardueの圧縮比較やEK公式そのものではなく、X_BHP_EKは未証明。

## 残る正確な義務

- X_BHP_EK：任意標数のlex存在、同じ全Hilbert関数での全graded Betti比較、proper lex idealの実極小生成元からのEK解消/実Tor計算。
- W_EDGE：最小幅のAP source/target識別と、一欠落coreの実作用・±1小行列・包含族単射・上端補正。
- W_DENSE：欠落prefixによる元のHx評価、一つの全Hilbert関数lex idealでのK調和計数、actual全行への容量差の支払い。q=3の資源とq≥4の閉鎖を分離する。
- W_FIVE：u=6/7の条件付き改善、非antipodal距離和、antipodalの実QC presentationと全行支払い。
- W_CLOSE：上の未完幅分岐を全物理狭幅へ合成すること。疎幅一分岐の完成で代用しない。

これらを入力する未証明structure fieldやaxiomを加えていない。Run19/20の担当は保持し、今回のPARTIALを完成runとしてrun数を進めない。

## 具体例の計算方法

`tests/WidthSparseData` と `WidthSparseCache` はメモリ対策の検算専用補助である。当該固定Dataの四重和以降がintervalになることを帰納で証明し、次数0–3の直接計算と合わせ、全次数で元のoffsetSumsに一致することを証明した。これから元のcomputedMinima/order/survivors/socleWindowとの等式を導き、43の既存受入を同じ内容で検証する。この表はW_SPARSEの一般証明には使わず、native_decide・未証明certificate・異標数rank一致も用いない。

## 2026-11-14 継続実装（上の未完一覧は11月13日時点）

- `DenseVolume` は半分超の有限群集合の二重和を鳩の巣原理で全群と同定し、同じ実Dの距離尾和からW=q+1+2t、P≤W、元のR≤tを証明した。素数位数・各offsetのunit性を要求しない。
- `DenseHeight` は長さ2以上の生存prefixが内部offset/0の剰余に入れず、互いに異なることを実endpoint factorと元のminimalityから示す。Hx≤u−q−1はdense以外にも成立する。`DenseResources` はこれからHx≤t、t≤2で元のR=0を得る。`dense_resources_closed` は凍結したRequested.DenseResourcesそのものを証明する。W_DENSE全体には未証明のDenseClosureが残る。
- `EdgeAP` はu=q+1の実offset集合から実AP sourceを識別し、元のSの全行比較まで戻す。d=1ではsource/targetのcarrierを同定し、d≥2ではV≥u+1と実AP公式を使う。一欠落幅u=q+2のKoszul rankは未完なのでW_EDGE全体は開いたまま。
- `FiveSmall` はu=6,7の全行actual比較を供給する。u=7かつ元のR>0の場合にだけHx≥3から実QCの高次基底の存在を導き、h2+q+2≤Pと第四調和上界でb1≤9を得る。R=0ではb1≤10を使う。原稿のτによる第一行改善と異なる十分な実証明であり、特性2/3で体内除算しない。
- 小幅高次行は既存の実rank envelopeで十分だった。第二行の44（u=6）、68（u=7）は原稿の40、62より弱いが、targetの46、77以下。原稿のより強い数値式を証明済みとはしない。
- `FiveHigher` はu≥8の全構造で第2行以上を閉じる。u=8は実尾和からW≤14、第2行のu≥9は非負多項式2z³+33z²+136z+33（z=u−9）で払う。第3–5行はC(u,k)/u²の分母を払った単調性（k=4,5,6）とu=8の基点を使う。これはantipodalの実QC presentationを証明したという主張ではない。
- `FiveNonAntipodal` は実fourPoint_growthからW≤growthVolume(u,4,3)を得て第一行を払う。u=8..11は同じ一般距離和の四つの算術基点、u≥12は6W≤u²+u+6からの非負多項式で処理する。元のS/任意体/literal targetの全行比較をexportした。

依然として五ID X_BHP_EK、W_EDGE、W_DENSE、W_FIVE、W_CLOSEは未完。残りは一般のBHP/Pardue/EK、一欠落coreの実rank、一つのlex商とdense容量、antipodal第一行/実presentation、それらの全域合成である。既存のW_SPARSEと凍結受入は変更しない。

## 2026-11-14 第2継続：W_FIVEの凍結契約を閉鎖

- `AntipodalCore/Basis` は同じDの実core点を三つの内部文字の個数で表示し、端点因子を持つyz,z²,zwと次数hの純語を除く。孤立zと次数n<hの(y,w)語の全単射を実CoreMinimalIndexへ構成し、`P=C(h+1,2)+1`を証明した。使うのはgcd(t,h)=1であり、gcd(t,u)=1を仮定しない。
- `AntipodalPresentation/Ideal` は生存指数の単射と係数ごとの実kernel判定から、元の内部変数環でliteral ideal `(YZ,Z²,ZW)+(Y,W)^h` の商を実QCへ同定する。`BinaryMonomialPower` が最後の冪を文字どおりのideal冪と同定する。元の変数像、単項式の標準次数、同じ多項式作用のmodule同型、実totalBettiの一致まで供給し、群のunitでGを置き換えない。
- `AntipodalVolume` はFin h×Fin 2と同じDの剰余の全単射を作り、全距離を評価して元のW=h²−h+2を証明する。
- 第一行は原稿の厳密式b1=h+4を経由せず、実Pの上界、既存の第三調和上界、元のR≤W−uから十分な比較を証明する。h=4はW≤14、h≥5は非負多項式を使う。厳密式b1=h+4は一般Lean定理としては未証明で、有限検算例のみ。この別経路は同じW_FIVE契約を追加前提なしに閉じる。
- u=5の四つの元のoffset集合を分類する。内部欠落2種類は `FiveHoleKernel` が実核の5生成元xy,xz,y²,z²,x³を証明し、`FiveHoleTopRank` が元のKoszul微分に3×3の符号付き単位小行列を構成する。b1≤5,b3+3≤Pと実Eulerからb2≤7を得る。端欠落2種類は元の向きのまま次数2基底のoffset一意性からP≤5を導く。元のR=0を通し、全行を実target下界へ払う。
- `FiveComparison` はu=4のAP、u=5、u=6/7、u≥8の二構造を網羅する。元の任意S、任意体k、物理幅V=d*u、各環自身のactual最小変数列、全iを保持する。`audit/run18/FiveClosedGoals.lean` の `NSP14.Run18.five_closed` が変更していない `Requested.W_FIVE` を証明する。

最新の未完はX_BHP_EK、W_EDGE（q≥4の一欠落）、W_DENSEのlex/閉鎖、W_CLOSE。DenseResourcesとAP半分は既に証明済み。Run18全体はPARTIALのままであり、五生成元閉鎖だけで一般のBHP/EKや全域幅比較を証明したとはしない。

## 2026-11-15：一般一欠落幅の閉鎖（Run18継続中）

最新closed IDはW_SPARSE,W_FIVE,W_EDGEの3件。X_BHP_EK,W_DENSE,W_CLOSEは未完で、Run19着手はユーザー指示で保留した。

`EdgeHoleGeometry` は元のaのcardから一意な欠落hと、実minimal語次数≤2、二次生存offset h/h+uを導く。`OneHole` はhの範囲と元のalphabet等式だけを持ち、比較結論やrank証明書を含まない。
`EdgeHoleAction` は欠落の左右の実内部変数にmate involutionを構成する。各線形係数は同じ側の唯一のpartnerにだけ二次基底成分を持つ。`EdgeHoleMinor` は各target wedgeに存在する欠落partnerから、元のKoszul slotへの挿入と符号付き対角単位minorを構成する。`KoszulCombinedMinor` は一次/二次係数の実交差成分が0であることを用いてunit minorと合成する。全証明は任意Fieldで、標数2でも±1は単位である。
`EdgeHoleWedgeCount` は全blockを含むwedge数をguard付き二項係数で数え、`EdgeHoleCounting` は二つの補正の和をactual targetの二つの補正以下に抑える。負添字をNat飽和減算で別係数に変えない。原稿のexact rank/Betti等式を一般定理としては主張せず、actual chain rankの十分な下界を証明した。
端欠落では二次offsetの一意性からP≤q+2、内部欠落では元のdense資源P≤q+3、いずれも元のHx≤1とR=0を使う。`narrow_oneHole_comparison` は元のS/物理幅/独自の最小変数/完備接錐を保持する。既存のAP比較と合わせた `edge_closed` が凍結W_EDGEそのものを閉じる。
`SourceNormalization` は任意Dの実sourceのoffsetGcd=d、normalizedWidth=uを証明し、m=du+2,d=3のactual source fixtureへ適用した。

`Lex/Stable` は元のlex条件から同次数の変数引上げ閉性を任意標数で導く。`Lex/MonomialGenerators` は実monomial membershipから最小divisorを構成し、Dicksonにより実極小生成元集合の有限性とideal span等式を証明する。これはEK解消や一般BHP比較の代用ではなく、X_BHP_EKは閉じていない。

2026-11-15 ordinary EK追加：IsLex.ordinary_ekは実極小生成元の全ordinary寄与を証明。実colon/完全列/変数null-homotopyと補変数の正則除去を使う。内部次数付きEKとBHP比較は未証明であり、この追加をRequested.X_BHP_EKの閉鎖とはしない。

## 2026-11-15：元のgraded EK契約の実証明

2026-11-15 graded EK：`NSP14.Run18.ek_closed : Requested.EK` が元の凍結契約そのものを証明。properな実lex ideal、任意体、全i≥1・全j∈Int、実極小生成元集合に対して、商の内部次数deg(v)+i−1と寄与C(max(v)−1,i−1)を保持する。実斉次像/商map、実grading shift、実colon SESの次数付き加法性、座標商のgraded集中を構成し、実生成元順で有限帰納した。座標商は非Artinも含み、有限k-chainの仮定を加えていない。
focused02は7 fixture＋公理probeの8 commandが個別exit0/警告0。実lex ideal(X0,X1²)の全positive row/全internal degreeの式をQ/F2/F3で検査し、生成元の異なる次数と商の一段ずれを確認。root6102jobs成功。主要5exportの推移公理はpropext/Classical.choice/Quot.soundだけ。元のRequestedGoals hash不変、旧verification/artifactのbyte変更なし。以前のR06 coldは新規追加前の記録で、現在追加の全回帰はまだ。

BHP/Pardueと全Hilbert関数lex存在は未証明。X_BHP_EKを閉鎖と数えない。

## 2026-11-15：実初期idealと三角作用の準備
InitialIdealはすべての非零ideal要素の実leading exponentから構成し、元のstandard exponent集合との一致と元の斉次商の全Hilbert関数保存を証明。任意非零pのprincipal idealの実initial idealも同定。NormalTriangularは実商の一意なnormal代表のleading termが増えず、nonstandard単項式のnormal代表は厳密に低いtermだけを持つと証明。InitialActionは同じ実商/基底の変数作用へ接続。nonstandardの実作用を0と誤認せず、同じblock以上の係数0を証明した。
TriangularBlockRankは元の写像の各対角block rangeの実基底と実前像・射影から、全体の実微分の単位三角minorを構成し、対角rankの和≤全rankを証明。有限性はtargetのみで、非Artin商のfull coefficient chainを有限k次元とはしない（後でinternal-degree chainへ適用）。4 named fixture＋公理probeの5command全exit0/警告0、root6110jobs成功。主要6exportの推移公理は許容三公理のみ。
これらは初期idealへのactual graded Betti比較そのものには未接続で、BHP/EK全体の閉鎖ではない。最後のcold R07は8b1921d sourceのEKまでを認証し、この4moduleは含まない。追加後cold全回帰は未実行。次はactual graded chain基底/augmented exponent blockと実initial quotientのblock一致を構成し、三角rankから全β_{i,j}(I)≤β_{i,j}(in(I))を閉じる。BHP/Pardueのlexへの変形・全Hilbert lex存在・dense/globalも未完、Run19は保留で継続する。
