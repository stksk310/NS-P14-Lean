# Run20 独立数学監査（Main 合成・全域分割）

対象: `/workspace/NS-P14-Lean-run18`、branch `audit/run20-20261116`、HEAD `a5e122a4d09536b1609c5faa8d419f8faf81671f`。

判定: **PASS（下記の読解scopeに限定）**。Mainの全称型、実対象、6分岐の被覆と適用、凍結契約の数学的意味について、修正を要する問題は検出しなかった。Critical / Important / Minor の指摘は0件。

これは実行PASSではない。Lean、Lake、checker、packagerは一切実行していない。既存レビューやGREENログの結論を根拠に採用していない。repo/source/evidence/cacheを変更せず、報告のみこの `/tmp` ファイルへ保存した。有限probeも用いていない。

## 読解対象と限界

全行を読んだ中心scopeは `NSP14/Main.lean`、`NSP14/Main/{IntervalTarget,Partition,Branches}.lean`、`audit/run20/{RequestedGoals,PartitionClosed,ClosedGoals}.lean`、受入2本、`tests/Main*.lean`、`tests/Run20Contracts.lean`、V06第6章と第1章BRIDGE/CAP/MINCAPである。

実出口から、SmallEmbedding Base/ThreeComparison/LanTuVu、Ordinary Closure/NumericalBettiClosure/ActualWitness/RelativeRowsAll/ActualTorRow、NarrowFour Comparison/HigherRows/FirstLarge/SmallWidths/WidthFourComparison、Width Closure/FiveComparison/DenseComparison/SparseComparison/EdgeAP/EdgeHoleComparison/FiveHoleComparison/AntipodalComparisonを追った。さらに実定義・transportを Basic/Atoms/IntervalCompletion(All)/WidthNormalization/ActualCutRank/CarrierTransport/FormalSemigroupRing/FormalTangentAlgebra/CompletedComparison、Homological Betti/Presentation/ActualTorTransport/ActualCoefficientBaseChange、Endpoint Presentation/Normalization/FullTransfer、Target IntervalBetti/IntervalAPBetti/APLowerRows 等で確認した。ordinaryのrank/空塔について QuadraticCutRank/NumericalClosure/ActualResources/ActualLayers/TowerResources/TowerRow も読解した。

この監査はMainとその直近の数学的接続の独立監査であり、全推移依存の各低水準補題を新たに一から再証明したとの主張ではない。cold kernel再検証はcoordinatorの担当である。

## 1. 最終型・凍結契約・実対象

- `NSP14/Main.lean:10` の公開定理の引数は S、k、`[Field k]`、任意自然数 i のみ。e≥2、幅、比較certificate、Infinite、CharZero、i≤e等の追加前提はない。左右とも `FormalTangentAlgebra k` で、各自の `AtomExponent` / `FullPolynomialRing k` を用いる。右辺は文字どおり `S.intervalCompletionAll`。
- `audit/run20/RequestedGoals.lean:14` の I_MAIN は同じ全称型（targetをletで束縛するだけ）。`ClosedGoals.lean:6` は公開定理をその契約へ直接渡す。受入 `acceptance/I_MAIN.lean:4` は名前付き `main_closed` をこの契約型で要求している。
- `RequestedGoals.lean:8` の I_PARTITION は唯一領域、実cut条件、実narrow正規化を含む。`PartitionClosed.lean:5–7` はこれを個別のproduction theoremで充足する。受入 `acceptance/I_PARTITION.lean:4` は契約定義の存在だけでなくclosure証明を要求する。
- 歴史比較も読取実施した。`git diff 996d982 HEAD` で RequestedGoals、受入2本、IntervalCompletionAll に差分なし。初期 `996d982` の Partition 定義群と現在の定義本文は一致し、差分は OffsetOrder import と後続証明追加。`parameterRegion` / `cutRegime` / `cutParameters` / `narrowRegime` / `narrowParameters` を True 等へ置換した意味の弱化はない。
- `tests/Run20Contracts.lean:10–11` の `example : Prop := ...` 自体は閉鎖証明ではない。本体と受入は別に実証明を要求しており、この区別は保たれている。

実対象も追った。`Semigroup/Basic.lean:12–15` はcofiniteな実加法部分モノイドで、conductorは最小性を要求しない証人。`Atoms.lean:12–13,31–45` の原子は実正元の分解不能性、`Homological/Presentation.lean:37` の AtomExponent はその実原子。`FormalSemigroupRing.lean:15–17,42,68–69` は S にsupportを持つ実形式級数と定数項kernel、`FormalTangentAlgebra.lean:15–22,171` はそのイデアル冪の逐次商の直和である。`Homological/Betti.lean:15–18,41–46` は有限生成多項式加群のKoszul homologyのk次元で、通常のTorへの接続もある。数値profileを実接錐に代入して定理を自明化していない。

## 2. literal target と conductor transport

- `Semigroup/IntervalCompletionAll.lean:17–20` のcarrierは常に `closure (Icc S.multiplicity S.maxAtom)`。元のconductor証人を使い、元のSがこの閉包に含まれることからcofinitenessを得る。e=1も含む。
- he≥2では旧 `intervalCompletion` のAP実装とのcarrier一致が `IntervalCompletionAll.lean:25–27` と `IntervalCompletion.lean:46–50` にある。旧APの幅が `min(w,m−1)` でも、生成されるcarrierがliteral区間の閉包と一致するため、狭い仮想targetへの置換ではない。
- `Main/IntervalTarget.lean:10–16` は両側completed_totalBettiを代数的接錐へ戻し、`CarrierTransport.lean:42–47` の同carrier Betti一致を使う。conductorの等式を仮定していない。CarrierTransportの代数的実対象はcarrierに依存し、cofinite証明の差は証明無関係性で消える。完成側は `completedPolynomialLinearEquiv` を経由するので多項式作用も保たれる（Presentation:156–169、ActualTorTransport:30–33）。
- `tests/MainTargetTransport.lean:9–20` はcarrier=⊤、conductor=17の別証人を明示し、同carrier transportを全k/iで適用する。`25–39` はsource e=2、target e=3の実例でtarget側独自変数を保持する。

## 3. 全域分割と境界

- `Main/Partition.lean:11–18,47–66` は e=1,2,3、e≥4かつw≥m−1、e=4かつw≤m−2、e≥5かつw≤m−2 の唯一領域を証明する。e≥4ならm≥e≥4を用いられるので、Nat減算でも最後の2幅範囲に重複・整数の穴はない。w=m−1はordinary、w=m−2はnarrow。
- `Partition.lean:23–27,68–79` は実actualCutRankについて2≤r≤e−1、r=2/3/4..8/≥9、r≥9⇒e≥10、r≥3⇒C(r+1,2)≤δ、δ=0⇒r=2を証明する。rank2へ三角下界を誤適用しない。`ActualCutRank.lean:17` は実degreeSet 2のcardからrを定義し、QuadraticCutRank:62–75はr=max(2,p)の例外を明示する。
- 空塔は排除されない。`TowerResources.lean:39–40` はIcc 2 qTopDegreeの和、`81–87` はδ=0時その区間が空で全towerResource=0になることを証明。`Ordinary/NumericalClosure.lean:108–119` はrank2をδ>0の前提なく扱う。MainがcutParametersを直接使わなくても、ordinary実出口自身が同じ実rankと同じ実towerを使うため接続に循環はない。
- `Partition.lean:33–41,81–99` と WidthNormalization:145–178,180–206 は、元のm、q=e−2、d>0、u≥q+1、**d*u=w**、m≥d*u+2、gcd条件、generators=元のatoms、source.carrier=元のcarrierを供給する。mをdで割った別半群にしない。e=4ではu≥3、e=5ではu≥4、e≥6ではu=e−1/e、e+1..2e−3、u≥2e−2が尽きる。

## 4. 実branch出口と元の体

`Main/Branches.lean:19–44` は各出口へその領域条件だけを渡し、右辺を同carrier Betti transportでunconditional targetへ運ぶ。Main:17–25は唯一領域の存在部分を6通りに分解してこれらへ接続する。

- e=1: SmallEmbedding/Base:15–47で唯一原子1、S=ℕ、literal targetと同carrierを導く。Base:80–89はBetti列(1,0,...)も証明する。Mainではcarrier一致を用いるので幅0の未定義offsetや正幅APIを要求しない。
- e=2: Base:91–161で実2原子のAPと同carrier、Betti列(1,1,0,...)を得る。Base:174–187は第0行、第一行の実target容量、他行0を分け、全幅を覆う。
- e=3: ThreeComparison:217–238は全幅をnarrow/ordinaryに分ける。narrowはu=2 full APとu≥3の実one-letter profile、ordinaryは同じ元のSへのordinary出口。uの仮想targetではなくphysical capacity（87–96）へ運ぶ。V06 §6.1の公刊LTV引用そのものを形式公理として置く経路ではなく、必要な比較を直接証明する十分な別証明である（同ファイル184–185が範囲を明記）。主張の弱化ではない。
- ordinary: Closure:16–27は完成source/完成実targetの全i比較。NumericalBettiClosure:68–77はcanonicalActualWitnessを元のSから作り、InfiniteScalarField上の実source Betti上界を `actualG_totalBetti_baseChange` で元のkへ戻す。ActualWitness:10–17に任意profile/comparison fieldはなく、ActualCoefficientBaseChange:196–200は実多項式加群のbaseChange同型とBetti一致を使う。最終source/targetともkのまま。
- e=4 narrow: Comparison:30–78は第0行、高次行、第一行を分ける。第一行はu=5/≥9、有限小幅、u=4,d=1,a={1,3}の特殊族を尽くす。特殊族はm≥6から全剰余類m mod4へ進む全m証明（WidthFourComparison:272–362）で、mの有限確認ではない。d≠1の幅4枝はSmallWidths:679–688でphysical w≥8を明示して支払う。
- e≥5 narrow: Width/Closure:16–38はe=5を別処理し、e≥6はfull AP、one hole、sparse、残るdenseへ分ける。FiveComparison:13–33はu=4/5/6..7/≥8を覆う。DenseComparison:57–80、SparseComparison:10–48、EdgeHoleComparison:70–97はu≤wとmin(w,m−1)=wを使って実physical targetへ運ぶ。EdgeAP:67–113のd=1最小幅は同carrier、d≥2ではw≥u+1を使う。非最小幅の容量を最小幅へ無理に適用しない。

## 5. 全行・topの区別・循環

- 公開型も全branch出口もiの上限を要求しない。Endpoint/FullTransfer:54–64はsource top=q+2をactualRで抑え、その**上**だけを消滅させる。topをi>eと取り違えていない。
- N4 HigherRows:186–233はi=2/3/4/それより上を分け、必要な幅4/5のtop=4は実消滅証明を使う。ordinary RelativeRowsAll:19–41とNumericalBettiClosure:15–61はrelative terminal/Euler行とH0補正を保持する。
- `tests/MainBoundaryRows.lean:8–16` は0、source e、e+1、target eTを別に適用する。`19–35` の例はsource e=4の第5行0に対しtarget e=6の第5行5を実公式から示す。sourceの消滅からtarget消滅を推論していない。
- Main/Partitionは実数値・正規化補題のみから証明され、Mainの比較やbranch閉鎖を仮定しない。Main/Branchesと確認したproduction出口にもMain/audit/testsを逆importする箇所や比較結論を追加引数として受ける箇所は見つからない。確認したspanではsorry/admit/数学axiomで閉じる箇所も見つからなかった。ただし全推移依存の公理集合の認証結果をここで主張するものではない。

V06第6章・BRIDGE/CAPに対する結論は、元の全S、任意Field k、全i、両側自身の実最小変数、literal完成targetという必要契約を保持した合成である。実行と全推移依存のkernel認証については別のcold再検証結果を待つ。
