# 実行スレへの指令：Run18 / BHP–EKと五生成元以上の物理狭幅閉鎖

> **For agentic workers:** Use `superpowers:executing-plans` inline, preserving the execution thread's authorized workflow and model. This order does not request additional agents or model changes.

**Goal:** 全体20 run計画のRun18として、任意標数のBigatti–Hulett–Pardue比較・Eliahou–Kervaire公式を実証明し、edge・dense・sparse・五生成元の各分岐を、元のactual sourceとliteral interval completionの全Betti行比較まで閉じる。

**Architecture:** 公刊入力の正確なgraded Tor契約を先に固定する。Run16の同じ向きのQC・P・R・Hxと、Run17の巡回成長・実Wのexportを使い、edgeの実行列、denseの一つのlex商、sparseの距離多項式、五生成元の小幅/antipodalを証明する。最後に正規化前の数値半群へ戻し、各環のactual最小変数列で比較する。

**Tech Stack:** Lean `v4.36.0-rc2`、mathlib `139105d28c7685a154cb3093f79edb2e16708099`、既存Python検証。

**Spec:** [全体20 run計画](2026-11-10-p14-20-run-roadmap.md)、[V03依存表](../../../proof_structure_v3/P14_DEPENDENCY_MAP_V03.md)、[幅側本文](../../../proof_structure_v3/work/WIDTH_PART.md) V.1–V.4、[V02](../../../proof_integrated_v2/NS_P14_INTEGRATED_PROOF_JA.md) §1.2(2), §13.2–13.5、[読解監査](../../../auditability_search/LATER_READABILITY_AUDIT.md) §3, §7。

## Global Constraints

- 作成時の公開workは`c4fd8153f55bb231aab4168a47c1546888fa7ab0`。Run17の公開記録は二IDをCOMPLETEと報告しているが、この監査スレのRun17独立監査はまだ実施していない。着手時に最新work、到着済みの監査修正、実exportの型と依存を読み、採用SHAを記録する。公開フラグだけを独立監査合格と表示しない。
- 担当閉鎖IDは下表の六つ。`X_BHP_EK`をdenseの数値式だけに縮めず、元の任意体・同じ全Hilbert関数・全graded行の契約を保持する。原典名のaxiom、結論を持つ未証明structure field、同じ比較を引数にしたwrapper、有限offset表は閉鎖にならない。
- 一つの長いrunで、公刊入力、actual consumer、修正、全検証、原稿台帳、監査引継ぎ、通常Pushまで進める。小補題・数値部分・内部commitで終了しない。30〜60分を硬い上限にせず、context圧縮後も継続する。20 runは目標であり、数学的な完了条件を弱めない。
- 固定toolchain/mathlib、既存数学source・検証原本・ZIPを保持する。許容公理依存は`propext`・`Classical.choice`・`Quot.sound`のみ。既存の証明に必要な修正は差分・理由・再検証を記録し、旧証跡を更新して辻褄を合わせない。
- **物理狭幅を固定する。** `e=q+2≥5`、`0<a₁<…<a_q<u`、`d≥1`、`V=d*u`、`m≥V+2`、`gcd(a₁,…,a_q,u)=gcd(m,d)=1`。QCは同じ正規化整数core、`P=P_C`、Rは元のGの端点socle、Hxも元の向き。Run16の広いEH条件`u<m`だけに最終scopeを広げない。`d=1`・`gcd(m,u)=1`・Cohen–Macaulay性・`P_C=P_G`を追加しない。
- targetは幅Vの**実際の**`S.intervalCompletion he`。正規化幅uの仮想targetや、sourceと同じ変数数のtargetで置き換えない。Run15のAP公式・幅の下界とRun16の正規化/完備接錐同値を使う。正の行では`Fmin_i(u)=i*C(u,i+1)+min(C(u,i−1),C(u,i))`を実target以下の下界として使えるが、sourceが常にこの下界以下だとは仮定しない。反射・群のunit作用をactual GやR/Hxの保存とみなさない。
- Run19にはN4のsocle三角形・混合語の最終計数・小幅・LTVと一〜三生成元、Run20には全域分割と主定理合成を残す。本runは五生成元以上の物理狭幅を完了する。
- 以下の新規module・宣言名は設計候補。入口と結論の意味を保持して既存APIへ合わせる。別の十分な実証明を使う場合は原稿との差を記録し、公刊入力IDの元契約も閉じる。

| 閉鎖ID | 必須出口 |
|---|---|
| `X_BHP_EK` | 任意体・同Hilbert関数lex商への全graded Betti比較と、lex生成元のEK寄与 |
| `W_EDGE` | `u=q+1,q+2`のactual全行比較、内部/端欠落と上端補正 |
| `W_DENSE` | `q≥3,0≤t≤q`の資源、および`q≥4,2≤t≤q`の全行支払い |
| `W_SPARSE` | `e≥6,u≥2e−2`の第一行全小e分岐と全高次行 |
| `W_FIVE` | `e=5,u≥4`の小幅・非antipodal・antipodal全域 |
| `W_CLOSE` | 任意体・五生成元以上・全物理狭幅・全iのactual completion比較 |

## Review Focus

1. **任意標数の公刊証明。** char 0のgeneric initial idealの強安定性を正標数へ流用しない。必要なら同標数の無限体へ拡大して戻す。各体の実Torを比較し、異なる標数のrank一致は仮定しない。
2. **同じ全Hilbert関数の一つのlex ideal。** 各次数の都合のよい独立なlex集合ではない。ideal性・存在・有限生成・実graded quotientとの対応を証明する。未証明の自由分解/比較towerを入力しない。
3. **整数・有理数と係数体の分離。** incidence重みや1/2,1/3は有理計数。char 2/3の体内除法にしない。負の下添字の二項係数は0で、`Nat`の飽和減算で別の係数へ化けさせない。
4. **実核を補償した同じsource。** `FullTransfer`等のactual QC→G比較を通す。QCのHilbert関数だけから非monomial quotientのBetti値を断定しない。edgeのrankは実作用・符号付き単位小行列で証明する。
5. **範囲と上端。** dense資源のq=3とdense閉鎖のq≥4を分ける。五生成元u=7の改善はR>0だけ。i=0、i=e、source消滅後のi、d=1のsource=targetを最後まで保持する。

---

## Task 1：現状API・原典・凍結した受入命題を固定する

**Files:** `audit/run18/RequestedGoals.lean`、`docs/RUN18_INPUT_INVENTORY_JA.md`。**Consumes:** `Endpoint/Normalization`・`CoreArtinBasis`・`CoreInternalAction`・`CoreHilbert`・`FirstHarmonic`・`FullTransfer`・`RowPackage`、Run15の`Target/IntervalAPBetti`、Run17の`Additive/EndpointVolume`・`CyclicAntipodal`。

- [ ] 最新workを取得し、Run16監査`5ced6cc564e5c69bebcd7a852463091e2e276661`とRun17の公開証跡・到着した独立監査を確認する。既存moduleの実型を読み、`Endpoint.Data.wordVolume_tail`・`wordVolume_growth_bound`、`NSP14.Additive.fourPoint_growth`等から必要なconsumerまでの対応を記録する。未監査と未証明を区別する。
- [ ] 固定mathlibと既存projectを意味・型まで再検索する。過去の[ライブラリ調査](../../../lean_planning/P14_LEAN_LIBRARY_AUDIT.md)は正確なBHP/EKを発見できていないという限定的結果である。既存の`MinimalFreeTower`や初期加群のAPIが比較を供給済みだとは仮定しない。
- [ ] [Juhnke-Kubitzke–Venturello §2.2 Lemmas 2–3](https://link.springer.com/article/10.1007/s40306-021-00449-8)と参照先のBHP/Pardue・EK証明を読む。必要な圧縮/変形・辞書順ideal・解消の依存を分解する。既存Lean証明を再利用できる場合は、取得URL・commit・license・元source hash・適応差分・固定版でのビルドを保存する。引用名だけでは証明にならない。
- [ ] 六IDの元の全称命題をProp定義として凍結する。`X_BHP_EK`は任意体k、標準次数多項式環T、斉次Iと同じHilbert関数のlex Lについて、実`β_{i,j}(T/I)≤β_{i,j}(T/L)`および下記EK式。幅側は同じactual source/targetの任意i比較であり、比較結論を含む追加前提を持たせない。
- [ ] Run16の正規化前SとDの一致、V=d*u、e=q+2、元のR/Hx、各体の実Tor有限性を入口一覧にする。受入moduleは宣言不在の段階で失敗を保存する。仕様の定義だけを実証明と数えない。

**Acceptance:** `tests/Run18Contracts.lean`で通常/explicit型を検査する。正標数を排除するinstance、physical幅をuと取り違えたtarget、lex比較やW_CLOSE自体を仮定に残したsectionがないことを確認する。

## Task 2：任意標数のBHP/PardueとEKを実証明する

**Files:** `NSP14/Lex/Ideal.lean`・`Hilbert.lean`・`BettiComparison.lean`・`EliahouKervaire.lean`、必要な依存module。**Tests:** `LexHilbert.lean`・`LexBetti.lean`・`LexEK.lean`。

- [ ] 標準次数・一つの固定変数順でのlex ideal、各次数の標準単項式基底、同じ全Hilbert関数のlex商の存在を実装する。graded pieceの有限次元性を明示する。一般の斉次商の契約をArtin商だけへ縮めない。
- [ ] 原典に従う任意標数の実比較を証明する。採用する初期ideal/圧縮/変形の各段階について、Hilbert関数保存と実graded Koszul/Tor次元の非減少、停止/帰納を供給する。char 0版だけ、数値Macaulay展開だけ、比較結論付き証明書のconsumerだけで止めない。
- [ ] properなlex（又は十分なstable ideal）の極小単項式生成元vについて、変数番号`max(v)∈{1,…,q}`を固定し、商のi行への寄与`C(max(v)−1,i−1)`、内部次数`deg(v)+i−1`を証明する。実自由分解又はlinear-quotient/実Tor計算から導き、ideal自身のi行との一段ずれを避ける。単位idealの商は0として別扱いし、生成元1へ未定義のmax(v)を適用しない。
- [ ] `β_{i,j}(T/L)=Σ_{v minimal, deg(v)+i−1=j} C(max(v)−1,i−1)`、i≥1をexportする。有限生成による有限台とgraded→totalの和を証明し、既存`gradedBetti`/`totalBetti`への同一性を結ぶ。I=0や単位ideal等の境界は契約に沿って処理する。
- [ ] 有限体は同標数拡大で処理する場合、ideal/lex Hilbert関数・最小生成元・actual Bettiの基底変換をすべて接続する。自然数の係数をk内で割らない。

**Acceptance:** 同じHilbert関数を持つ非lex斉次商とlex商を具体化し、実graded Bettiの非自明な比較を検査する。lex/stableの複数生成次数を含むEK式、i=1/q/q+1、内部次数のずれを検査する。少なくとも`ℚ`・`ZMod 2`・`ZMod 3`で同じ契約を適用し、特性0限定の証明を排除する。

## Task 3：最小幅・一欠落幅の実coreと全行を閉じる（W_EDGE）

**Files:** `NSP14/Width/EdgeCore.lean`・`EdgeKoszul.lean`・`EdgeComparison.lean`。**Tests:** `WidthEdge.lean`・`WidthEdgeRank.lean`。

- [ ] `u=q+1=e−1`はfull AP source。Run15の実AP公式を使い、正の全行を`i*C(u+1,i+1)`以下に抑える。`d=1`はsource=targetで直接閉じる。`d≥2`では`V≥2u≥u+1`とtarget第一項が払う。d=1を小さすぎる一般下界`Fmin(u)`で無理に払わない。
- [ ] `u=q+2`の欠落h∈{1,…,u−1}について、次数nのQC基底を`nB \ ((n−1)B ∪ ((n−1)B+u))`で同定する（B={0,…,u}\{h}）。h₀=1,h₁=q、n≥3で0。内部欠落の次数2基底はoffset h,h+u、端欠落はh=1ならu+1、h=u−1ならu−1。元のHx≤1からR=0を得る。
- [ ] 内部欠落ではr=h−1,s=u−h−1,r+s=q、r,s≥1。実内部作用の二つのpermutation blockから任意標数の単位小行列を構成する。`ρ_i=2*C(q,i−1)−C(s,i−1−r)−C(r,i−1−s)`、`b_i=i*C(q+1,i+1)−2*C(q,i−1)+T_i`、`T_i=C(s+1,i−r)+C(r+1,i−s)`を証明する。負添字を0にするguardを明示する。
- [ ] 二つの包含族への単射を実構成して、`T_i≤min(C(q+2,i−1),C(q+2,i))`を示す。像の衝突・空の場合・上端を含める。`P=q+3,R=0`と実transferを通して、target最小補正との差`min−T_i`を閉じる。
- [ ] 端欠落ではP=q+2、permutation rankを証明し、`β_i≤i*C(q+2,i+1)+[i=q]+[i=q+1]`を得る。二つの指示項を残し、actual targetの補正がそれぞれ1以上で払うことを示す。反射をcoreの補助識別に使っても、Rの評価は元の向きで証明する。

**Acceptance:** 内部欠落と両端欠落、r=1/s=1、char 2、i=q/q+1/q+2を名前付き定理で検査する。d=1とd>1、`m=du+2`のactual source/target比較も通す。

## Task 4：欠落prefix・一つのlex商・dense支払いを閉じる（W_DENSE）

**Files:** `NSP14/Width/DenseResources.lean`・`LexHarmonic.lean`・`DenseComparison.lean`。**Test:** `WidthDense.lean`。

- [ ] `t=u−1−q`、資源範囲q≥3,0≤t≤qで、生存する内部標準語の長さ2以上のprefix剰余が相異なる欠落offsetであることを証明する。既存offset/0なら端点表示、重複なら零和部分語になる実core関係を使い、語長≤t+1、元のHx≤tを得る。
- [ ] 実剰余集合Aのcard=q+1>u/2から距離≤2、欠落剰余の距離=2を証明し、`W=q+1+2t`、`P≤W`、`R≤t`、t≤2ならR=0をexportする。q=3の資源は五生成元でも使える型にする。
- [ ] Task 2の一つのlex idealで、`S_j(n)`を最初のj変数に支持された次数n標準語数と定義する。極小生成元数`g_j(n)=S_j(n−1)−S_j(n)+S_{j−1}(n)`を加法形又はIntで証明し、有限台でtelescopeする。EKから`b_i(QC)≤i*C(q+1,i+1)+K*C(q−1,i−1)`、`K=Σ_{n≥2}Σ_{j=1}^q S_{j−1}(n)`を得る。
- [ ] `C(r+1,2)≥2t,r≤q`なら高次lex標準語が末尾r変数に支持されること、子の計数`M_n=Σ_j S_j(n)`、指数重みincidenceを証明する。`K≤Σ_{n≥2}(r−1)h_n/(n+1)≤2t(r−1)/3`を有理計数で導く。既存Artin親子計数と共通化してよいが、今回のKとの同一性を省略しない。
- [ ] 閉鎖範囲はq≥4,2≤t≤q。`A_i=C(q−1,i−1), C_i=C(q,i−1), B_i=C(q+1,i−1)`とし、差を一つに固定する：`D_i=i*(C(q+t+1,i+1)−C(q+1,i+1))−(q+1+2t)*C_i−R*B_i−K*A_i`。
- [ ] Vandermondeのj=1,2項から、t=2ではr=3・整数性K≤2・R=0により`D_i≥(q−3)C_i+i*B_i−2*A_i≥0`。t=3ではK≤4,R≤3により`D_i≥(2q−4)C_i+(3i−3)B_i−4*A_i≥0`。各i=1と上端も実際に閉じる。
- [ ] t≥4ではr=tを使い、`D_i≥[(5t²−17t−6)/6+(t−1)(q−t)]*C_i≥0`。t=4+z,q=t+vなら括弧の6倍=`5z²+23z+6+6zv+18v`。全1≤i≤q+2でsource≤target第一項を結び、i=0/消滅後も含める。

**Acceptance:** q=3の資源、q=4,t=2/3/4、q=tの境界、t=0/1のedgeとの整合、char 2/3、最上端を検査する。dense閉鎖の型にq=3を紛れ込ませない。

## Task 5：疎幅の距離多項式と全高次行の橋を閉じる（W_SPARSE）

**Files:** `NSP14/Width/SparseVolume.lean`・`SparseFirst.lean`・`SparseHigher.lean`・`SparseComparison.lean`。**Test:** `WidthSparse.lean`。

- [ ] e≥6,u≥2e−2、a=e−1,s=ceil(a/2)=floor(e/2)。Run17の同じDの成長/尾和から`W≤B=u+Σ_{j≥0}(u−a−s*j)_+`を得る。有限和への切断と尾の0を証明する。合成数uと非自明stabilizerを保持する。
- [ ] Δ=u−a=s*k+b,0≤b<sで`B=u+Δ²/(2s)+Δ/2+b(s−b)/(2s)`、`B≤B*=u+Δ²/(2s)+Δ/2+floor(s²/4)/(2s)`を証明する。また`B≤u²/a`の差の2a倍は` s*(2s−a)*k²+a*s*k+2*(2s−a)*k*b+2*b²`。分母正値とNat/Int/ℚ変換を処理する。
- [ ] actual E_ARTIN/E_TRANSFERへP≤B,R≤B−uを代入し、第一行の二上界`(e+3)B/3−u+e(e−1)/6`、`(e+5)B/4−u+(e−1)e(e+1)/24`、高次の`U_i=B*C(e,i)−u*C(e−1,i−1)−C(e−1,i+1)`を導く。引き算前の非負性又は加法形を保持する。
- [ ] 第一行はtarget下界`C(u,2)+1`へ支払う。z=u−(2e−2)で、e=6,7,8,9はB*を使い差をそれぞれ`z²/24+43z/24+1/2`、`2z+1`、`3z²/32+63z/16+211/32`、`z²/16+17z/4+29/4`と証明する。e≥10は第一上界とB≤u²/(e−1)により`(e−1)(e−10)/2+1+(4e−33)z/6+(e−9)z²/(6(e−1))>0`。
- [ ] 第二行は幅側本文V.3のe=6,e=7,e≥8を個別に閉じる。e=6は差≥`(u−10)(u−3)(u+1)/3`。e≥8はe=8+v,u=2e−2+zで中括弧`2v²+5vz+16v+2z²+26z+18`、e=7は`2z²+21z+4`。実際のU₂との恒等式・不等式を証明し、多項式の正値だけでsource接続を省略しない。
- [ ] 全2≤i≤eへ、`T_i(u)=i*C(u,i+1)/C(e,i)+u*i/e+(e−i)(e−i−1)/(e(i+1))`を導入する。`i*C(u,i+1)≥U_i ↔ T_i(u)≥B`を正分母で証明する。`T_i(e)=e−1+i/e`、幅増分`i*C(u,i)/C(e,i)+i/e`、u≥eでの隣接比を証明し、`T_i≥T₂≥B`を幅の帰納で導く。i=eを別途含め、i<e用の分母e−iを上端で使わない。
- [ ] すべての支払いを元のactual Gへ戻し、`V≥u`とRun15のtarget下界で実completionへ接続する。「第二行が通れば全行」だけの省略を残さない。

**Acceptance:** e=6/7/8/9/10、u=2e−2と次の幅、Δ mod s=0/s−1、i=2/e/e+1、非自明なdと合成数uを検査する。有限係数検算は補助であり、全称証明はLeanの恒等式・帰納で閉じる。

## Task 6：五生成元の小幅・四点例外・全高次行を閉じる（W_FIVE）

**Files:** `NSP14/Width/FiveRows.lean`・`FiveSmall.lean`・`AntipodalCore.lean`・`FiveComparison.lean`。**Tests:** `WidthFive.lean`・`AntipodalActual.lean`。

- [ ] e=5,q=3。三変数Artin商の`b₁≤P+2,b₃≤P−1`と実Euler特性からb₂≤2Pを導き、actual transferで第2–5行を`(5P+4R,4P+6R−1,P+4R,R)`以下にする。u=4,5はTask 3へ接続する。
- [ ] u=6はdense資源P≤8,R=0と整数性からb₁≤8、β₁≤16。u=7はP≤10,R≤3,b₁≤10、R=0ならβ₁≤20。R>0なら元のHx≥3からQCの次数4が非零、τ=Σ_{n≥3}h_n≥1を示し、`b₁≤6+2(P−4)/3−τ/6<10`、整数性b₁≤9、β₁≤22を得る。
- [ ] 第2–5行の上界はu=6で`(40,31,8,0)`、u=7で`(62,57,22,3)`。Run15の実target下界`Fmin`はそれぞれ`(46,60,39,11)`、`(77,126,119,56)`。表の有理算術だけでなく、前項のactual rowsからこの表を経由して接続する。
- [ ] u≥8の非antipodalはRun17の実`fourPoint_growth`を適用し、`W≤B₃=u+Σ_{j≥0}(u−4−3j)_+`。u=3j,3j+1,3j+2でB₃は`(3j²+j+2)/2,(3j²+3j+2)/2,(3j²+5j+4)/2`。β₁≤floor(5B₃/2−u+5)、床前のtarget差は`(3j²+j−26)/4,(3j²+3j−22)/4,(3j²+5j−24)/4`。u≥9の該当j≥3を閉じ、u=8はB₃=13、床上界29を保持して払う。
- [ ] antipodalはu=2h,h≥4、実集合A={0,t,h,t+h}、0<t<h、gcd(t,h)=1。gcd(t,u)=1は要求しない。**同じ実QC**の基底と作用から`QC≃k[y,z,w]/(yz,z²,zw,(y,w)^h)`を次数・内部変数対応付きで証明する。n<hの(y,w)語と孤立zの生存、次数間剰余の分離、次数hの端点表示を示す。群のunitによるGの同型で代用しない。
- [ ] 実presentationから`P=C(h+1,2)+1,b₁=h+4,W=h²−h+2`を得て第一行を払い、targetとの差`(h²+h−12)/2≥0`を証明する。単にこのmonomial idealを新しく定義しただけでQCとの同定を済ませない。
- [ ] 両構造でP≤u²/4,R≤u²/4−uを導く。第2行の差は`u*(4u−7)*(u−8)/12≥0`。残りの粗い上界は`(5u²/2,5u²/4,u²/4)`、u=8のtarget第一項は`(210,224,140)`。固定k=4,5,6の`C(u,k)/u²`の単調性を証明して全u≥8へ延ばす。

**Acceptance:** u=4/5/6/7/8/9、u=7のR=0とR>0、非antipodalとantipodalを含める。antipodalはt=1だけでなく、例えばu=10,h=5,t=2（gcd(t,u)≠1）でも実presentationを適用する。char 2/3、元のR>0、全5行を検査する。

## Task 7：全物理狭幅をactual completionへ合成する（W_CLOSE）

**Files:** `NSP14/Width/Closure.lean`、`audit/run18/ClosedGoals.lean`。**Test:** `WidthActualClosure.lean`。

- [ ] e≥6は`u=e−1,e`、`e+1≤u≤2e−3`、`u≥2e−2`、e=5はu=4,5,6,7とu≥8の二構造で、順序付きoffsetからu≥e−1を供給して全域を覆う。境界の穴や重複による追加仮定を残さない。
- [ ] 正規化前の任意の数値半群S、任意体k、`5≤S.embeddingDimension`、`S.width≤S.multiplicity−2`、全iについて、`S.FormalTangentAlgebra k`のactual最小変数列での`totalBetti`が、`(S.intervalCompletion he).FormalTangentAlgebra k`のactual最小変数列での`totalBetti`以下、という公開定理を証明する。完備/代数的接錐の同値を既存exportで通す。
- [ ] i=0は両辺1。1≤i≤eを各分岐へ、i>eはsource=0とtarget非負へ接続する。sourceより変数が多いtargetの高い行を誤って0にしない。
- [ ] `RequestedGoals.lean`の元の六命題を変更せず同時に証明する。主要宣言の通常/explicit型、source/targetの環・変数対応、ID→証明→consumerの経路を保存する。中間の資源構造へ最終比較を埋め込んでいないことを見直す。

**Acceptance:** physical最小m=du+2、d=1/d>1、幅分岐の両側、i=0/e/e+1およびtarget自身の上端、非CMでR>0/P_C≠P_Gとなる実sourceを含むfixtureを用意する。有限fixtureは全称閉鎖定理を実際に適用し、数値checkerだけを全域証明と表示しない。

## Task 8：全回帰・不変証跡・原稿台帳・公開

- [ ] 各Taskは受入型を先に固定し、実装後にfocused build/test、内部commitを行う。重要な受入は名前付き定理で保存し、匿名exampleだけのmoduleを宣言監査の網羅性に数えない。
- [ ] `scripts/verify_run18.py --fresh-test-cache`等で全既存fixtureと新fixtureを実依存順に実行する。空のtest cacheと新規production lib/irの再構築を含め、古いoleanに依存しない。Run15/16/17の元の契約も回帰する。
- [ ] Run17の不変証跡方式を継承し、新しい`verification/run18/runs/<unique-id>/`だけへ出力する。既存出力先を拒否する。旧数値checkerの固定出力先はtemporary rootへ隔離し、Run01–17の検証記録・timestamp・ZIPをbyte照合で保持する。回帰実行で過去原本を再生成しない。
- [ ] Lean環境から全新規宣言・instance・constructor/recursor・生成helperとroot-moduleの公理依存を抽出する。許容三依存以外、`sorryAx`、自己依存を拒否し、通常/explicit型・module・source hashを保存する。grepだけで公理監査を済ませない。
- [ ] 境界/整数/有理数の独立checkerで上記の表・多項式を再検算する。実core/Tor fixtureをℚ・標数2/3で実行する。理想のHilbert関数だけの検査、有限offset全列挙、異標数rank一致は一般証明を代替しない。
- [ ] `docs/RUN18_CLOSURE_STATUS.json`、原稿対応表、未完宣言一覧、監査引継ぎ、検証JSON、source/evidence hash、COMPLETE又は正直なPARTIAL ZIPを確定する。六IDの成否を分け、閉じたconsumerと未完の公刊入力を区別する。
- [ ] verifier・packager・数値入力・凍結受入もhashへ含める。証明snapshot、検証snapshot、review対象commitを実git bytesで束縛し、review後の変更を未審査のまま公開済みと数えない。ZIP全entry/hash/CRC、証跡欠落・既存出力上書き・source差替え・review snapshot不一致へのguardを検査する。
- [ ] 通常commit/Push後、実remote SHAとclean worktreeを確認する。work取得は`git fetch origin refs/heads/work:refs/remotes/origin/work`等で行う。並行更新を保持・統合し、force Pushしない。Run19/20へ渡す実export・残る正確な型・所要作業を記録する。

## 終了条件

**任意標数のBHP/Pardue・EK、edgeの実Koszul rank、denseの一つのlex商、sparseの全高次行への橋、五生成元の条件付き小幅改善とantipodal実presentationが、元のactual sourceからliteral completionの全行比較へ追加の未証明比較前提なしに接続し、六ID・全検証・台帳・通常Pushが揃った時にRun18完了とする。**

BHP/EK未証明のまま数値評価だけ完成、char 0のみ、有限offset表のみ、QC比較のみ、第一行のみ、物理幅をuへ置き換えたtarget比較はこの終了条件を満たさない。実際の障害は、閉じたexport・未完の正確な型・必要入力・理由を保存し、未完をCOMPLETEにせず残りRun19–20を再校正する。

このファイルは実行スレへ貼り付け/参照するための指令である。監査スレからの直接送信やRun18の証明実装は行っていない。
