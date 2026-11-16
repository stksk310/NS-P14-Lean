# 実行スレへの指令：Run19 / N4全幅・幅4全m・一〜三生成元のactual閉鎖

> **For agentic workers:** REQUIRED SUB-SKILL: Use `superpowers:executing-plans` inline to implement this plan task-by-task. Preserve the execution thread's authorized workflow and model. This order does not request extra implementer agents or model changes. Steps use checkbox syntax for tracking.

**Goal:** 本来のRun19担当10 ID（N_DISTANCE, N_WORDS, N_HIGH, N_FIRST, N_SMALL, N_WIDTH4, N_CLOSE, I_BASE, X_LTV, I_THREE）を、任意体・元のactual完成接錐・literal interval completion・全Betti行の証明付きexportまで閉じ、全検証・台帳・通常Pushへ進む。

**Architecture:** Run16の二内部変数QC/socle/元のRと実四行評価、Run17の三点成長とSC二ラベルconsumerを使い、N4の実標準語downsetから距離・socle三角形・混合語長・一括計数を証明する。幅6–8の短い代数的場合分けと幅4の全multiplicity証明を合わせ、四生成元の物理狭幅全域へ戻す。一〜三生成元を別に閉じ、Run20へ無条件の出口を渡す。

**Tech Stack:** Lean `v4.36.0-rc2`、mathlib `139105d28c7685a154cb3093f79edb2e16708099`、既存のPython検証・不変証跡方式。

**Spec:** [20run計画](2026-11-10-p14-20-run-roadmap.md)のRun19、[V03依存表](../../../proof_structure_v3/P14_DEPENDENCY_MAP_V03.md)の上記10 ID、[幅側本文](../../../proof_structure_v3/work/WIDTH_PART.md) V.5–V.10、[N4置換証明](../../../n4_further_reduction/N4_PAPER_REDUCTION_JA.md)、[V02](../../../proof_integrated_v2/NS_P14_INTEGRATED_PROOF_JA.md) §§1.2(5),14.2–14.6,16、[読解監査](../../../auditability_search/LATER_READABILITY_AUDIT.md) §§2,5。原稿は数学的仕様・証明所在であり、そこに「既証明」とあることをLean実装済みの根拠にしない。

## Global Constraints

- 作成時の最新workは `58a0f54651916a4f7d6aa2e172d9250d91fd25f4`。Run18はPARTIALで、閉鎖はW_SPARSE/W_FIVEのみ。R05は183 command・169 fixture、実公理依存8942宣言、新規701宣言を検査した。着手時には最新workと到着済み監査修正を取り直し、採用SHA・差分・実exportを確認する。
- **担当の境界を保持する。** Run19番号へ進んでもRun18を完了扱いしない。X_BHP_EK/W_EDGE/W_DENSE/W_CLOSEの4義務は `audit/run18/RequestedGoals.lean` の元の型のまま別台帳に残す。N4はこれらの未証明宣言を仮定せず進められる。Run18残務も実装した場合だけ、その型・証拠・検証を別に追加する。Run20の最終閉鎖にはRun18残務も必要。
- このスレは監査・指令作成側。**この指令を実行するのは実行スレ**であり、本ファイル作成をRun19の実装や監査合格に数えない。
- 一つの長いrunで実装、actual接続、修正、全検証、原稿台帳、監査引継ぎ、通常Pushまで継続する。30〜60分を硬い上限にせず、context圧縮後も同じ台帳から続ける。20runは目標であり、到達保証や契約を弱める理由ではない。
- 固定依存・既存数学source・既存検証原本・ZIPを保持する。`sorry`/`admit`/`native_decide`、追加の数学公理、結論入り証明書、同じ比較を引数にしたwrapperで埋めない。実依存は `propext`・`Classical.choice`・`Quot.sound` のみ。
- N4のscopeは `0<a<b<u`, `u≥3`, `d≥1`, `gcd(a,b,u)=gcd(m,d)=1`, **m≥d*u+2**。元のS、元のQC、P=P_C、sigma=実QCの内部socle、元の向きのHx/Rを使う。d=1、gcd(m,u)=1、各offsetのunit性、CM性、P_C=P_Gを追加しない。
- targetは物理幅V=d*uの実 `S.intervalCompletion he`。各環自身のactual最小変数列と `FormalTangentAlgebra k` を使い、uの仮想targetやsource変数数のtargetへ置換しない。unitは有限群の列にのみ作用させ、G/R/Hxが保存されるsource変換とは扱わない。
- 歴史的196組core証書、83 profile/665比較/5 tail、Navi増分を主依存に戻さない。幅6–8の有限な**紙上場合分け**は残す。全m/dの証明を有限fixtureや計算上の最大値へ置換しない。
- 完成・条件付き・未完、原稿どおりの式・十分な別証明を区別する。差異は `docs/LEAN_PAPER_ALIGNMENT_JA.md` とRun19対応表へ、式・仮定・結論・実宣言・影響を記録する。

## Review Focus

1. SCのunit/ラベル交換を、元の二内部文字の**同次数端点関係**へ戻せているか。反転sourceのRやHxを使っていないか。
2. socle点の個数ではなく、実QCの共通annihilatorとdownset極大点の対応・全三角形の包含まで証明しているか。
3. 幅4で長さが増える全競合の**K',L'両座標**、制限anchor、j=1への還元、非禁止語の実像の独立性まで供給しているか。
4. actual targetの下界の有効範囲を保つか。u=3,d=1、V=4、u=5第二行、m=6、sourceより高いtarget行を省略していないか。
5. LTVは原典の正確な仮定と任意標数性を確認した実証明か。理想/商の添字ずれ、e=1の幅0/空gcd、既存completion APIのe≥2制限を処理できているか。

---

## Task 1：実入口と10契約を固定する

**Files:** Create `audit/run19/RequestedGoals.lean`, `tests/Run19Contracts.lean`, `docs/RUN19_INPUT_INVENTORY_JA.md`, `docs/RUN19_CLOSURE_STATUS.json`。未完受入は `audit/run19/acceptance/`。

**Consumes:** `Endpoint/TwoRows`, `TwoInternal`, `InternalSocleBasis`, `TwoMonomial`, `SocleBounds`, `Additive/ThreePointGrowth`, `TwoValueSequence`, `EndpointVolume`, Run15のactual target/完成接錐比較。
**Produces:** 10 IDの元の全称命題、型・source・供給元一覧。最終比較の共通型は、e≥2では `Run18.Requested.Comparison S k he` と同じactual対象とする（未証明のRun18閉鎖宣言はimport/仮定しない）。

- [ ] 最新work/監査branchを明示fetchし、dirty実行checkoutを上書きせず、既存の隔離workspaceまたは適切なbranchを使う。Run18の元の凍結SHA `86a0a18eff0632cb915d67748dcef47a88991cebf287ef95750f58b450bea689` と未完4件を確認する。
- [ ] 10 IDをPropとして定義し、量化・scope・通常/explicit型を先に凍結する。N_DISTANCE/N_WORDS等を最終比較だけへ縮約せず、依存表にある資源/標準語命題も残す。e=1の契約はliteral interval carrierとの同一性・実Betti列まで固定する。
- [ ] 公開名候補 `NSP14.Run19.{distance_closed,words_closed,high_closed,first_closed,small_closed,width4_closed,narrow_four_closed,base_closed,ltv_closed,three_closed}` を要求する名前付き受入を実行し、不在によるREDを保存。指定不在以外のimport/構文エラーをRED成功に数えない。
- [ ] 既存 `actual_two_row_one/two/three/four` は**actualR版**、`actual_two_all_rows` はRhat版であることを記録し、必要な元Rの評価と混同しない。`internalSigma_point_count` を実sigmaへの接続に使う。
- [ ] `narrow_fullAP_comparison` は現状he≥5なのでe=4には直接適用できない。u=3,d=1のsource=targetは既存Run15のAP/carrier APIから別途供給する。

**Check/Commit:** 必要依存をbuild後、`lake env lean tests/Run19Contracts.lean` は契約定義/型の検査だけをPASS。各未完受入は指定unknown declarationのみでFAIL。定義作成を閉鎖と数えず内部commit。

## Task 2：実二変数downset・距離・socle三角形（N_DISTANCE）

**Files:** Create `NSP14/NarrowFour/CoreWords.lean`, `SocleTriangle.lean`, `Distance.lean`; tests `N4CoreWords.lean`, `N4Distance.lean`。
**Interfaces:** consumes Task1の実QC基底とsigma点数、`threePoint_growth`, `wordVolume_tail`; produces 同じDの標準語downsetとP/sigma/Wの等式・不等式。

- [ ] RED受入：同じ次数・offsetの二内部語は同一、実CoreMinimalIndexと有限標準指数集合の全単射、乗法/消滅と実内部socleの対応。
- [ ] y,zをD.aの順序付き二要素と同定し、実多項式作用と指数のdownward closureを証明する。単なる新しいmonomial modelの次元計数で止めない。
- [ ] 任意nで `|n{0,a,b}|≥min(u,2n+1)`、有限尾和から `W≤1+u²/4`（Nat床）を証明する。合成数u・非自明stabilizerも既存Kneser経路に含める。
- [ ] socle極大点を第一指数順に並べ、i番目が `(i,sigma-1-i)` を支配すること、全次数sigma−1の語と全約数が標準であることを示す。`C(sigma+1,2)≤P≤W`, `sigma≤u−1` を実sigmaでexport。
- [ ] 合成数u、個々のoffsetが非unitでもcollective gcd=1の例、階段型downset、sigma=1と端の極大点を名前付きテストにする。

**Check/Commit:** `lake build NSP14.NarrowFour.Distance` と上記2 fixtureがPASS、元契約N_DISTANCEもGREENになってから内部commit。

## Task 3：純語・SC混合語と元のheight（N_WORDS）

**Files:** Create `NSP14/NarrowFour/StandardWords.lean`; test `tests/N4StandardWords.lean`。
**Interfaces:** consumes Task2, `savchevChen_twoValue`, `normalized_modular_relation`; produces 標準語長・混合語長・元のHx/R評価。

- [ ] RED受入：全標準語 `s+t≤u−2`、混合 `s*t>0 → s+t≤u/2`（Nat床）、`P≤2u−3+C(u/2,2)`, `Hx≤u−3`。
- [ ] 純語はgcd周期または `q*a≡b mod u` の置換で次数u−1までに端点表示を持つことを実core点で証明する。
- [ ] 混合標準語が零和部分列を持たないことを、元の端点factor/minimalityから証明する。SCのラベル交換の両側を処理し、unit後の値1,cと個数R0,T0、`R0+c*T0≤u−1` を得る。
- [ ] `c*alpha≡beta mod u` を元の整数offsetへ戻し、同次数の端点表示 `Y_alpha^c=x^(c−1−k)Y_beta v^k` を構成。全指数の非負性・端点因子の正値を示して `R0<c`、従って `2(R0+T0)≤u` を導く。
- [ ] 元の座標 `Hx=max(s+t−ceil((a*s+b*t)/u))` を証明して `Hx≤u−3`、u=3,4の元のactualR=0をexport。unitや反射の後のheightで代用しない。
- [ ] u偶奇、長さちょうどfloor(u/2)、その直上、SCでラベルが交換される場合、char2/3で実QCへ適用するfixtureを実行。

**Check/Commit:** `lake build NSP14.NarrowFour.StandardWords`、fixture、凍結N_WORDS受入のGREEN。

## Task 4：第2–4行を全幅で閉じる（N_HIGH）

**Files:** Create `NSP14/NarrowFour/HigherRows.lean`; test `tests/N4Higher.lean`。
**Interfaces:** Task2/3 + actual二内部四行 + Run15 target → 元のSで全i≥2のcomparison。

- [ ] 実四行から `U2=5u²/4−2u+4`, `U3=u²−3u+4`, `U4=u²/4−u+1` の有理/整数上界を導く。係数体内で割らない。
- [ ] V.6の非負多項式をactual rowsへ接続：u=6+zで `12(L2−U2)=4z³+45z²+152z+108`、u=5+zで `8(L3−U3)=z⁴+14z³+67z²+134z+88` と `60(L4−U4)=2z⁵+30z⁴+170z³+435z²+458z+105`。
- [ ] u=5第二行は床を保持しP≤7,R≤2,sigma≤4から24≤target25。u=4は `(12,5,0)`、V=4の実target `(12,7,0)` を使う。u=3は実QC=(y,z)²商を同定し、d=1のcarrier一致とd≥2,V≥6を分ける。L3のV≥5制限をV=4へ誤適用しない。
- [ ] 元のSとDのBetti同一性、V≥u、literal targetの容量へ戻す。i>4はsource=0、target自身の高い行を0としない。
- [ ] u=3/4/5/6、i=2/3/4/5、d=1/3、m=du+2、任意体consumerとQ/ZMod2/ZMod3の実例を検査。

**Check/Commit:** build/fixture/N_HIGHの全量化受入がGREEN。

## Task 5：三関係の一括計数と第一行（N_FIRST）

**Files:** Create `NSP14/NarrowFour/Relations.lean`, `FirstCount.lean`, `FirstLarge.lean`; test `tests/N4First.lean`。
**Interfaces:** Task2/3 + actual第一行 → 元の全u=5またはu≥9の第一行比較と計数資源。

- [ ] 元のcoreで `y^b=x^(b−a)z^a`, `z^(u−a)=y^(u−b)v^(b−a)`, `y^(u−b)z^a=x^(u−b)v^a` を証明し、実downsetから各倍数を除く。
- [ ] h=u/2, k0=u−b+a, `E_h(k0)=if k0≤h then C(h−k0+2,2) else 0` とguardを固定する。純軸の単位元を一回だけ数え、禁止矩形の平行移動と三角格子点の全単射で `P+E_h(k0)≤2u−k0−1+C(h,2)` を証明。
- [ ] `k0+E_h(k0)≥h+1`、`P≤2u−h−2+C(h,2)`、混合socleの相異なる第一指数からsigma≤h+1を導く。Task2の**全三角形包含**を使い、sigma≥k0+1なら禁止語が標準になる矛盾からsigma≤k0も示す。
- [ ] 実R≤W−uとactual第一行へ戻す。偶数差h(h−5)/2、奇数差(h²−3h−2)/2を証明し全u≥9を払う。u=5はP≤7,sigma≤3,Hx≤2からR=0、第一行≤11。
- [ ] k0≤h/＝h+1/>h+1、u=5/9/10、奇偶の最小幅、実R>0の例をテスト。Nat飽和減算を無条件の二項係数にしない。

**Check/Commit:** build/fixture/N_FIRST受入のGREEN。有限幅の列挙だけで全uを認証しない。

## Task 6：幅6–8と幅3・4の短い場合分け（N_SMALL）

**Files:** Create `NSP14/NarrowFour/SmallWidths.lean`; test `tests/N4Small.lean`。
**Interfaces:** Task2–5 → u=3,4,6,7,8の第一行比較（u4,d1,a1,b3だけTask7へ）。

- [ ] u6：Hx≤2でR=0、第一行≤15。Hx=3なら次数/offsetと混合語長から(a,b)=(1,5)を強制し、yz=xvと純冪関係からP≤9,sigma≤2,R≤4、第一行≤16。
- [ ] u7：k0=2,3,≥5を一般式で閉じ、k0=4の(1,4),(2,5),(3,6)を関係式/strip antichainで16,18,16以下にする。
- [ ] u8：k0=2,3,≥7は一般式。k0=4の(1,5),(3,7)は28以下、k0=5の4対は21以下、k0=6の(1,3),(3,5),(5,7)は27,21,27以下。collective gcdによる除外も証明する。
- [ ] 幅3の唯一の対とd=1/d≥2、幅4のd≥2とd1の(1,2),(2,3)を扱う。後者は実downset⊆{1,y,z,yz}とP+sigma≤5を示す。単なるP≤4,sigma≤2の加算で5としない。
- [ ] 全例外対に名前付き任意m/d/Field定理を置く。有限mまでのdecideやPythonのexact core最大値は証明前提にしない。反射に頼らず元のRを評価する。

**Check/Commit:** build/fixture/N_SMALL受入がGREEN。例外対の網羅性とm=du+2・char2/3を含める。

## Task 7：幅4の最後の族を全mで閉じる（N_WIDTH4）

**Files:** Create `NSP14/NarrowFour/WidthFourCore.lean`, `WidthFourCompetitors.lean`, `WidthFourInitial.lean`, `WidthFourComparison.lean`; test `tests/N4WidthFour.lean`。
**Interfaces:** d=1,u=4,a=1,b=3,m≥6の実core/kernel/target → 全mのactual第一行比較。

- [ ] 内部重みwt(y)=1,wt(z)=2,wt(x)=wt(v)=0を先に、通常次数、固定lexと続くwell-founded monomial orderを構成する。実core四関係の候補initial ideal `J0=(y³,yz,xz²,z³)` に対し、自由列1,y,y²,zとx-free制限列z²の実像の独立性・停止除算を証明。
- [ ] 任意j≥1の自由anchorについて `r_j=(n−jm) mod4`, `kappa_j=(jm+r_j−n)/4`, lambda=(0,1,2,1), `Delta_j=lambda(r_j)−c−kappa_j−j` をIntで定義。**K'=K−kappa_j,L'=L−Delta_j** と非負性のiffを証明する。
- [ ] `4Delta_j<0`、制限anchorはK≥kappa_j+1で自由anchorに包含、kappa_jの単調性からj=1が正確な閾値。これをRun16の全競合核に接続し、j=1だけを仮定しない。
- [ ] `theta_n=max(ceil((m−n)/4),0)` は整数差を取ってから切上げる。`J=J0+(b*v^theta_n : b=1,y,y²,z,z²)`。禁止語のactual消滅と、非禁止語の最大分解長＝元の次数/同次数weightの相異性を証明し、**in(I_G)=J** を導く。Hilbert表や生成元候補数だけで等号を宣言しない。
- [ ] Jの極小生成元の先頭項を持つ実同次式を停止除算でI_Gの生成元へ持ち上げ、actual beta1≤mu(J)を供給。既存 `idealGeneratorNumber_le` を使う場合も、実sourceのdefining ideal/module/Torへの対応を証明する。
- [ ] m=6は上界6/target9。m>6,m=4Q+rhoでrho0/1/2/3の上界6/8/8/6、実target7/10/9/8を**全Q**で証明。m=6とm=7/8/9/10、任意Qの名前付き定理、char2/3を検査。

**Check/Commit:** build/fixture/N_WIDTH4受入のGREEN。有限m表を全m定理の代わりにしない。

## Task 8：元の四生成元Sの全幅・全行へ合成（N_CLOSE）

**Files:** Create `NSP14/NarrowFour/Comparison.lean`, `audit/run19/ClosedN4Goals.lean`; test `tests/N4ActualClosure.lean`。
**Produces:** `narrow_four_closed : Requested.N_CLOSE`。意味は任意S/k、e=4、S.width≤S.multiplicity−2、全iの実完成接錐とliteral interval completionの比較。

- [ ] endpointDataのq=2からu≥3、元のSとのcarrier/Betti同一性、V=d*u、元のRを供給する。
- [ ] 第一行をu3/4（Task6/7）、u5（Task5）、u6/7/8（Task6）、u≥9（Task5）で穴なく合成。i2–4はTask4、i0は双方1、i>4はsource=0で閉じる。
- [ ] N4の7 IDを凍結された型で証明し、証明を仮定に持つ最終wrapperにしない。source/target変数数が違う例、非CMでR>0/P_C≠P_G、m=du+2とd>1を含む実consumer fixtureを実行する。

**Check/Commit:** build/fixture/7受入GREEN。これだけでRun18 W_CLOSEやI_MAINが完成したとは表示しない。

## Task 9：一・二生成元と全Sで定義できるliteral target（I_BASE）

**Files:** Create `NSP14/SmallEmbedding/Base.lean`, `NSP14/Semigroup/IntervalCompletionAll.lean`; test `tests/SmallEmbeddingBase.lean`。
**Interfaces:** existing completionはhe≥2限定。全S用の候補 `intervalCompletionAll` を追加する場合、無条件のcarrier定理 `carrier=AddSubmonoid.closure (Set.Icc multiplicity maxAtom)` と、he≥2で既存completionとの一致を必須とする。既存APIは保持する。

- [ ] e=1なら原子が1だけでS.carrier=N、m=maxAtom=1と証明する。literal interval [1,1]の閉包がNであることからsource=targetを供給し、実Betti列(1,0,0,...)を計算。e1でtargetを便宜的にSと定義して同一性の証明を省略したり、he≥2や空集合gcdを要求したりしない。
- [ ] e=2の原子m<n、gcd(m,n)=1を実atomから抽出し、実接錐の最小表示をk[X,Y]/(Y^m)へ同定。k[[S]]の完成接錐との橋を通して商Betti(1,1,0,...)を証明する。
- [ ] actual interval target第一行≥1とi0一致を供給し、I_BASEを閉じる。targetの独自の上端をsource上端で消さない。
- [ ] S=N、<2,3>、<3,5>、幅0・ordinary境界、任意FieldとQ/char2/char3でテスト。

**Check/Commit:** build/fixture/I_BASE受入GREEN、全S completionのcarrierと既存API一致の受入GREEN。

## Task 10：LTVの実証明と三生成元consumer（X_LTV, I_THREE）

**Files:** Create `NSP14/SmallEmbedding/ThreePresentation.lean`, `LanTuVu.lean`, `ThreeComparison.lean`; tests `LTVActual.lean`, `SmallEmbeddingThree.lean`; provenance `verification/run19/sources/`。
**Spec:** [Lan–Tu–Vu arXiv:2307.05589v1 Theorem1.1](https://arxiv.org/html/2307.05589v1#S1)。原典全文と参照証明を読んで正確な仮定・対象を確定する。

- [ ] 固定ライブラリ/既存Lean形式証明を型まで調査し、原典又は証明済みの十分な特殊版から任意標数のactual比較へ至る依存を分解する。再利用sourceはURL/commit/license/hash/適応差分と固定版buildを保存。未取得の本文を取得済みとしない。
- [ ] 三生成元の実接錐defining ideal、原典が使う生成元/initial ideal/解消/実Tor比較を構成する。引用名のaxiom、有限例の実験、実自由解消の存在を未証明fieldとして入力したstructureで済ませない。
- [ ] 原典が理想のBettiなら商の正行へ一段ずらし、i0=1を補う。原典と同じ真のinterval completionへ接続し、各環のactual最小変数に運ぶ。原典の標数仮定が必要契約と違う場合は不足を実証明してから任意体をexportする。
- [ ] `ltv_closed : Requested.X_LTV`, `three_closed : Requested.I_THREE` を追加前提なしで証明。e=3全幅/全m/全iを閉じ、ordinaryだけのconsumerを全域証明として扱わない。
- [ ] CM/非CMの実三生成元、幅がm−2/m−1の両側、i0/1/2/3/4、char2/3で実定理を適用し、理想/商の添字を検査。

**Check/Commit:** build/2 fixture/2凍結受入GREEN。原典名付き一般入力を未証明のままconsumerだけ完成した場合、両IDを閉鎖に数えない。

## Task 11：全回帰・不変証跡・台帳・通常公開

**Files:** Create `scripts/verify_run19.py`, `check_run19_n4.py`, `package_run19_audit.py` と必要なguard; `docs/RUN19_{EXECUTION_LEDGER_JA,PAPER_CORRESPONDENCE_JA,FINAL_REVIEW_JA}.md`, `docs/RUN19_CLOSURE_STATUS.json`, `verification/run19/runs/<unique>/`, 新規監査ZIP。

- [ ] 全新規productionと全既存fixtureを実依存順にcold build/elaborationする。Run18 R05の169 fixtureと元の閉鎖契約を保持。各commandの終了コード・期待結果を個別に記録し、shell末尾の成功だけを全体成功の根拠にしない。
- [ ] 新規NarrowFour/SmallEmbedding/関連moduleのlib/IR、root/test/audit cacheを除いた検証を行う。依存共用cacheを破壊せず、空にした範囲・backup先を記録する。重いfixtureは必要なら -j1 -M12288を継承し、SIGKILL/OOM/失敗試行を成功へ書き換えない。
- [ ] 全新規・既存宣言・instance・constructor/helperの**実collectAxioms**、自己依存、通常/explicit型、module/source hashを採取する。exported theoremのaxiomInfoだけで追加公理と誤判定しない。隔離した実追加axiomを拒否するnegative controlはproductionへimportしない。
- [ ] 独立checkerでN4有理多項式・三角/矩形計数・小幅場合分け・幅4の四剰余を検算する。actual core/GのQ/char2/char3行列は各標数で独立計算し、一致を一般仮定にしない。
- [ ] 旧Run01–18の原本・timestamp・ZIPをbytes照合で保持する。旧checkerの固定出力をtemporary rootへ隔離し、出力は新しい排他的directoryだけ。失敗R01/R02や過去のPARTIAL ZIPを上書きしない。
- [ ] 10 IDそれぞれの元契約→実証明→actual consumer、Run18残務4件の現在の型/成否、原稿との差異、Run20へ渡す実exportを台帳にする。Run18の未完をRun19達成数へ混ぜない。
- [ ] verifier/packager/checker/凍結受入もsource hashへ入れる。source snapshot・evidence snapshot・review対象commitを実git bytesで束縛し、独立したwhole-branch reviewの結果と本文をbundleへ含める。guardはsource差替え・証跡欠落・review不一致・既存出力の拒否を検査する。
- [ ] COMPLETEは担当10 IDの元契約が全て閉じたときだけ。それ以外は正直なPARTIALを保存し、未完のexact型・必要な数学的接続・理由を列挙する。小補題の区切りや時間目安だけでrunを終えず、独立に進められる本runの残タスクを継続する。
- [ ] ZIPの全entry/hash/CRCを確認し、通常commit/Push後に実remote SHAとclean worktreeを確認。`git fetch origin refs/heads/work:refs/remotes/origin/work` 等でworkを明示取得し、並行更新は保持・統合、force Pushしない。実行先は事前に指定された通常branch/workを継承し、監査branchを勝手に上書きしない。

**Acceptance:** `python3 scripts/verify_run19.py --fresh-test-cache --output-dir verification/run19/runs/<new-id>` が全期待結果PASS。通常Pushと実remote確認まで記録。検証成功と数学的COMPLETEは別の判定欄を持つ。

## Run18残務との接続・Run20へ渡す条件

Run18残務の正確な型と次作業は [Run18台帳末尾](../../RUN18_EXECUTION_LEDGER_JA.md) と [凍結契約](../../../audit/run18/RequestedGoals.lean) を正本とする。最新commitで既に閉じていれば再実装しない。未完ならX_BHP_EKは一般斉次商の任意標数graded比較/EK、W_EDGEはq≥4の一欠落actual rank、W_DENSEは実lexと容量支払い、W_CLOSEは全幅合成を保持する。

N4・小生成元はこれらから独立に進める。余力という曖昧な理由で担当10 IDを小補題へ縮めず、公刊入力で停止した場合も残る独立タスクを進める。Run18残務の実装も継続するなら別IDの証拠として記録する。**Run19本来の10 IDが完成しても、Run18残務があれば全体は未完である。**

Run20はoriginal全域分割と主定理合成の担当とする。ただし未完のBHP/EK/LTV/幅閉鎖を仮定して「最終統合完了」としない。20run内の完成が難しいと判明したら実証明の不足をそのまま報告し、番号や表示だけで完成を作らない。

このファイルは実行スレに渡す指令書である。監査スレからの直接実行・クロススレッド送信は行っていない。
