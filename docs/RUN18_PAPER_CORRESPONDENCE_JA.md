# Run18 原稿対応（PARTIAL）

Run18全体は未完である。今回閉じた担当IDは **W_SPARSE** の一つ。残るX_BHP_EK・W_EDGE・W_DENSE・W_FIVE・W_CLOSEを完了扱いしない。

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
