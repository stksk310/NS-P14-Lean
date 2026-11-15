# Lean証明と最終原稿の対応・変更台帳

2026年11月10日（JST）作成。ユーザーは、証明が改善する変更を許容し、
最終的にLeanと論文を一致させられるよう記録を残すことを指定した。

この台帳は、将来の原稿改訂で使う数学的な差分を保存する。
履歴として固定したV02・V03や監査ZIPは書き換えない。
「Leanで証明済みの数値補題」と「actual対象との未接続部分」を区別する。
各項目は最終原稿への採否・反映と、最終Lean定理への依存を対応させて閉じる。

## A01：シフトの定義域（Block01監査修正）

- 原稿：`auditability_search/ORDINARY_PAPER_REDUCTION_JA.md` SO4–SO5。
- Lean：`SmallScalar.gap_shift`、`SmallScalar.small_gap_pos`。
- 対応：恒等式は任意の有理数シフト。正値性は `s,t : ℕ` と角条件の下。
- 影響：数学的な強化ではなく、不正確な「全整数」の表記の訂正。
- 最終原稿：SO4とSO5の定義域を分け、rank6–8でs=t=0を除くことを明記する。

## A02：Apéry–Sidonの入口（Block02）

- 原稿：SO1–SO2、V03 O_SIDON。
- Lean：`AperyPairData`、`AperyPairData.multiplicity_bound`、境界Sidon接続。
- 対応：二項和の数値最小性と数値的一意性を別フィールドに分けた。
- 影響：原稿の結論は同じ。ただしactual Q₂からこのデータを構成する橋は未実装。
- 最終原稿：この橋と反復項・異次数の衝突排除を保持し、局所仮定を無条件の結論と混同しない。

## A03：SO3の有限台とcutoff（Block03）

- 原稿：SO3、V02 (S3)–(S5)。
- Lean：`Resources`、`residual_tail_le`、`Resources.scalar_le_upper`。
- 対応：有限台Finsetと台外ゼロを明示し、台がcutoffより先まで延びる場合も同じ評価に含める。
- 影響：結論は同じ。SO3自体に不要なδ≥0やeの下限は構造体で重複要求しない。
- 最終原稿：非正の残余tailを落とす向きを明示する。actual towerから全条件を同時に供給する橋は残す。

## A04：低rankの有理数評価（Block04）

- 原稿：V02 §9、V03 III.1 O_LOW。
- Lean：`LowRank.rank_three_margin_pos`、`LowRank.Layers.rank_two_bounds`、`rank_three_bounds`。
- 変更：rank3の余裕を整数zの二項係数から評価する代わりに、直接の多項式分解で示した。
  z=δ−6、s=e−4とすると

  δ(V−1)−4(e+δ−7) = zs + z²/2 + 7z/2 + 2s + 15 > 0。

- 仮定・結論：e≥4、δ≥6の有理数まで成立する。元の整数の場合はそのまま含む。
- rank2：δ=0を含め、δ≥3やhead cap M−3を課さない。第一行の結論は非狭義で、V=3の等号を許す。
- 最終原稿：必要なら上の一行の分解に置換できる。実際のrank・target余裕への接続は別途保持する。

## A05：調和和障壁の増分比較の短縮（Block05）

- 原稿：V02 (S14)–(S19)、V03 O_LARGEの調和和帰納。
- Lean：`LargeSeed.harmonic_cutoff_step`、`barrier_step_identity`、`harmonic_lt_barrier`。
- 変更：凸性による両端平均と中間の2/rを介さず、各項を区間の最初の項で抑え、Bの増分と直接比較する。
- 同じ定義：a_r=r(r+1)/2、D_r=⌊a_r/2⌋+1、B(r)=r/4+1+9/(2r)。

### 最終原稿へ移せる代替証明

b=D_{r+1}−D_rとする。床関数の両側評価とa_{r+1}=a_r+r+1から
2b≤r+2、2(D_r+1)≥a_r+3を得る。従って

H_{D_{r+1}}−H_{D_r} ≤ b/(D_r+1) ≤ (r+2)/(a_r+3)。

r≥10、x=r−10≥0について、通分すると

B(r+1)−B(r)−(r+2)/(a_r+3)
= (x⁴+34x³+385x²+1472x+112) / [4r(r+1)(r²+r+6)] > 0。

初期値の正確な差は B(10)−H₂₈=1833472237/80313433200>0。
これを用いて帰納し、全r≥10でH_{D_r}<B(r)を得る。
この初期値は原稿と同じ不等式で、Leanでは28項の和を直接評価する。
T₁(r)>B(r)の正係数分解およびT₁(r)≤T_rは原稿のものを保つ。
r=9の基点は G₉(10,45)=5845533/7436429>0 と正確に評価する。
両方の有理数等式は `tests/LargeSeed.lean` でLeanが検査する。

- 仮定・結論への影響：同じr≥10の障壁、同じr≥9の基点G_r(10,a_r)>0。
  元の鋭い中間評価「調和和の増分<2/r」自体は主張しない。
- 最終原稿：上の代替証明を採る場合、主鎖から凸性補題(S14)と中間比較(S17)–(S19)を外せる。
  この局所置換で、基点から任意のδへの差分評価やactual接続が不要になったとは扱わない。

## A06：大rankの偶奇分岐を統合し、有理数まで閉じる（Block06）

- 原稿：V02 (S21)–(S31)、V03 (O22)–(O23)。
- Lean：`LargeScalar.floor_comparison_identity`、`baseStep_gt`、`quadrant_identity`、`large_gap_pos`、
  `SmallScalar.Resources.scalar_lt_large`。
- 対象：V03の大rank枝r≥9。V02の旧r=4,…,8の大rank枝は復活させない。
- 変更：F₀/F₁の偶奇分岐を、cutoffに関する一つの有理式比較に置換。
  r≥9の強い下界b₀>5/4を使い、δの整数性を不要にした。

### 最終原稿へ移せる代替証明

a=a_r、D=D_r、α=(r−1)/(D+1)、g₀=G_r(10,a)、A=G_r(11,a)−g₀、
b=G_r(10,a+1)−g₀とする。原稿の恒等式

g₀=(a+9)A+C、b=A+11−r−8α、C<0

とBlock05のg₀>0からA>−C/(a+9)>0を得る。
F(D)=−C/(a+9)+11−r−8αと置けばb>F(D)。
原稿(S25)のF₁を

F_min=a/2−3r/2+11/2+3(5r+31)/(2(a+9))−17(r−1)/(a+3)

と書く。連続的なcutoff比較の恒等式は

F(D)−F_min
= (2D−a−1)(r−1)(a²+17a+144) / [2(a+9)(D+1)(a+3)] ≥ 0。

最後の非負性はBlock05の床関数下限2D≥a+1による。偶奇の場合分けは不要。
r≥9ならa≥4rなのでa/2−3r/2+11/2≥11/2、(r−1)/(a+3)<1/4。
正の項を残せば F_min>11/2−17/4=5/4、従ってb>5/4を得る。

β=1−αと置くと0<β<1。有理数s,t≥0に対して、既存の二変数恒等式を

G_r(10+s,a+t)=g₀+sA+t(b−β/2)+β(t²/2+st)

と整理する。A>0、b−β/2>3/4であり、右辺は正となる。
これで全有理数e≥10、δ≥a_rについてG_r(e,δ)>0。
Block03の同じ資源列のSO3上界と合わせてF_r<δ(V+1)を得る。

- 仮定・結論への影響：r≥9は保つ。元の整数e,δを含む有理数全域へ強化する。
  有理数tに対してt(t−1)≥0と仮定することはなく、その負の一次項をbへ吸収する。
- 最終原稿：大rank枝では(S24)のF₀/F₁分岐を上の一式にし、(S30)の整数二項係数の評価を
  上の正二次式へ置換できる。actual資源列・Tor・Bettiへの橋は引き続き別に証明する。

## A07：全行scalar化の係数を明示（Block07内部単位1）

- 原稿：V02 (7.3), (10.1)、V03 O_SCALAR。
- Lean：`Scalarization.choose_balance`、`head_weight_eq`、`normalized_tail_le`、`row_le_scalar`。
- 結論：r≥4、1≤k≤rで、同じ非負有限層の第k行はC=choose(r−1,k−1)倍の第一行scalar以下。
  top行を含む。
- 対応：k choose(r−1,k)=(r−k)Cから重みを正規化する。
  headではW_k(1)=C(r+1)/(k+1)を直接示す。k≥2なら第一行のhead重み以下となる。
  tailではk≥3を分母比較、k=2を原稿の差の恒等式で処理する。
- 仮定への影響：数値的な有限層とH₀=δ≥0があればよく、actual Torの意味はまだ入力されていない。
- 最終原稿：正規化の二項係数関係とheadの上式を一行ずつ加えると、例外処理とtop行の監査が容易になる。

## A08：target余裕をδ方向の差分で短縮（Block07内部単位2）

- 原稿：V02 (8.2)–(8.4)、V03 (O15)–(O16)。
- Lean：`TargetMargin.target_zero`、`target_step`、`capacity_step`、`target_margin`。
- 変更：余裕の完全なVandermonde展開(8.3)を経ず、明示したR_kの差分から必要な(8.4)を直接得る。

### 最終原稿へ移せる代替証明

e,δは非負整数、r≥1、k≥1とする。原稿の式を

R_k(δ)=(e−r+k) choose(δ+r−1,k)+k choose(δ+r−1,k+1)、
L_k=(e−1) choose(r−1,k)−choose(r−1,k+1)

と書く（係数は整数/有理数の減算。実際の適用ではe≥r+1）。
隣接二項係数の関係とPascalから

R_k(0)=L_k、
R_k(δ+1)−R_k(δ)=(e+δ) choose(δ+r−1,k−1)
≥(e+δ) choose(r−1,k−1)。

δ回足し合わせると

R_k(δ)−L_k ≥ [eδ+δ(δ−1)/2] choose(r−1,k−1)
=δ(V+1) choose(r−1,k−1)。

- 仮定・結論への影響：(8.4)と同じ結論。形式的な二項式評価としてはk≤rを要求せず、δ=0も含む。
  任意のprofileからtargetのBetti公式を導いたという意味ではない。
- 最終原稿：(8.3)の正確な余剰Γ_kを別用途に使わないなら、その展開と直後の評価を上の短い証明に置換できる。
  actual targetの公式とTorからの移行は残す。

## A09：ordinary数値部分の全域を一本に統合（Block07内部単位3）

- 原稿：V03 O_LOW/O_SCALAR/O_SMALL/O_LARGEの数値部分とO_TARGETの余裕。
- Lean：`NumericalClosure.Data`、`Data.all_rows`、`all_rows_of_apery_pairs`。
- 入力：同じ有限層、2≤r≤e−1、総量、H₁≤rδ、tail cap。
  三角数下限とhead capはr≥3のときだけ要求し、rank2のδ=0を許す。
  r=6..8かつe=r+1の境界でだけSidon証拠または数値Apéry-pairデータを要求する。
- 出力：1≤k≤rのすべてで L_k+Σ_t W_k(t)H_t≤R_k。
  rank2/3の直接評価、4..8の自然数シフト、9以上の大rank評価を実際に合成する。
- 最終原稿：別々に証明した数値評価を一つの「共通資源の数値閉鎖」補題としてまとめられる。
  actual towerから全入力を同時に作る証明と、c_k≤L_k+ΣWHを与えるTorの証明は別途必要。
  `Data.relative_rows` は後者を明示した入力として受け取る入口であり、それ自体をactual Tor証明とは数えない。

## A10：actual半群からApéry・最小生成系・orderを構成（Block08）

- 原稿：V02 §2、V03 O_COORDの数値座標、SO1のatom/Apéry入力。
- Lean：`NumericalSemigroup`、`multiplicity`、`apery`、`closure_atoms`、`atom_mem_of_generates`、
  `order_realized_by_atoms`。
- 表現：数値半群はcofiniteなAddSubmonoid ℕと、あるconductorの証明で定義する。
  conductorの最小性は不要。multiplicityは正元の最小値として構成し、各剰余の最小元もNat.findで構成する。
  Apéry集合の濃度mとx=ω+qmの一意分解、predecessor不在の特徴付けを証明する。
- 最小生成系：mとApéry中の原子から有限集合を作り、Sを生成すること、任意の生成集合に含まれることを証明する。
  eはこの集合の濃度。0<e≤mが結論であり、仮定ではない。
- orderの定義：まず正の半群元への分解長の最大値を、n≤xという有限上界から構成する。
  最長分解の各因子が原子であることを証明したので、原稿の「最長生成元表示長」と一致する。
  正元への分解を原子への分解と無断で読み替えていない。
- 最終原稿：数学的な主張は同じ。存在・有限性・原子表示との一致を基礎補題として明記するとLeanとの対応が明確になる。

## A11：Apéry次数計数とterminal/headの数値段階（Block08）

- Lean：`degree_zero_card`、`degree_one_card`、`highSet_card`、`degree_two_le_deficit`、`apery_order_bound`、
  `terminalHeadEquiv`、`jump_le_of_live_base`、`jump_le_of_live_head`、`live_iff_of_equal_jump`。
- 完成：actual数値Apéry集合上で、次数0は1点、次数1はe−1点、次数≥2はδ=m−e点。
  二次層の濃度≤δ、全Apéry元のorder≤δ+1を証明する。
- νの上界の数値証明：最長原子表示から一原子を外すと、残りもApéryでorderがちょうど1減る。
  よって最大orderまで各次数が存在し、次数2,…,orderの相異なる代表をhighSetへ単射にしてorder−1≤δを得る。
- terminal/head：order(x+m)>order(x)+1というterminalと、liveなincoming m-arrowがない非Apéry headを数値的に定義する。
  x↦x+m、逆y↦y−mで全単射。terminalは正でjump≥2、head次数≥3。
  liveなbase作用ではjump非減少、liveなhead作用では非増加、同jumpならlive条件が一致する。
- 未完：これら数値集合をactual completed-semigroup tangent coneとその商・核の基底へ同定する環/加群の証明。
  globalなT≅Nは主張しない。同jump stratumの加群同型、jump≤ν、actual塔・資源・Torは後続工程。
- 最終原稿：上の数値補題と、actual環への同定を二段に分けて記述できる。数値段階だけをactual環の形式化完了とは数えない。

## A12：正元イデアルの全冪と数値orderの一致（Block09）

- 原稿：V02 §2、V03 O_COORDの「数値座標[v]は次数order(v)」という入口。
- Lean：`orderIdeal_eq_pow`、`mem_positiveIdeal_pow`、`positiveIdeal_eq_atom_span`、`positiveIdeal_isMaximal`。
- R=k[S]はactual半群の加法モノイド環。𝔪は正元単項式の生成イデアルとして定義する。
  係数で切る集合を𝔪の冪と定義して済ませず、両包含を証明した。
- 証明：order(v)を実現する正元分解の単項式積からtᵛ∈𝔪^order(v)。
  冪の降下性と各支持単項式の和からorder≥nの多項式⊆𝔪ⁿ。
  逆包含はorderの超加法性とイデアル積の帰納から得る。
- actual原子の和因子を最長原子表示から取り出し、𝔪が最小生成系の単項式で生成されることも示す。
  定数項写像の積保存はℕの非負性から証明し、全射・核=𝔪を得る。kが体なら𝔪は極大。
- 仮定：冪の同定は任意の可換係数環。tᵛの所属・非零判定には非自明性、極大性には体が必要。
- 最終原稿：座標補題の最初にこの冪所属補題を置ける。完備半群環との比較定理は別途必要。

## A13：次数付き商の単項式基底と積を構成（Block09）

- Lean：`leadingMap_ker`、`leadingMap_surjective`、`gradedPieceEquiv`、`gradedPieceBasis_eq_monomial`、
  `gradedMul_mk`、`gradedMul_monomial_layers`、`gradedMul_monomial_ne_zero_iff`。
- 分母は𝔪ⁿの内部の実次冪𝔪ⁿ⁺¹。order=nの係数抽出の核がこれに等しく、
  任意の有限支持座標は0拡張で持ち上がる。第一同型定理からGₙの基底を構成した。
- 有限性の短い証明：conductor証拠Cを固定する。v≥(n+1)(C+1)なら
  vはn個のC+1と残りv−n(C+1)≥C+1の和なのでorder(v)≥n+1。
  従ってorder(v)≤nならv<(n+1)(C+1)。Cは最小でなくてよい。
- 代表の両側の変更が積を次冪だけ変えることを示し、実商上へ双線型積を降ろす。
  積の値は次数和の層でのt^(u+v)のクラス。order(u+v)>order(u)+order(v)なら0、
  等号なら非零。この非零判定は非自明係数環kの下で成立する。超加法性があるため他の場合はない。
- 最終原稿：冪→係数抽出→基底→積という順で入口のactual性を明記できる。
  本Blockでは直和環としての結合則・単位元のパッケージと完備化の比較をまだ構成していない。

## A14：terminalとactual単項式のx核の一致（Block09）

- Lean：`xAction`、`xAction_monomial_eq_zero_iff`、`monomial_mem_xKernel_iff`。
- actual乗算Gₙ×G₁→Gₙ₊₁の片側を[tᵐ]で固定してx作用を作る。
  非自明係数環kの下で、そのactual核へ[v]が入る条件は、Block08で定義したTerminal vと一致する。
- これは数値terminalをactual kernelに接続する最初の構成である。
  核全体の基底、Aのhead基底、N/Q、同jump strataの加群同型は未完。
  globalなT≅Nは導いていない。
- 最終原稿：数値ラベルの全単射と、商・核・作用の代数的同定を区別して引用する。

## A15：実冪の次数付き商を全可換k代数へ組み立て（Block10）

- 原稿：V02 §2 / V03 O_COORD冒頭のGの数値座標と積。
- Lean：`pieceGCommRing`、`TangentAlgebra`、`pieceGAlgebra`、`tangentCoordinates`、`tangentBasis_eq_initial`。
- Block09で作った実商Gₙと双線型積から、結合則・単位元・交換則・整数の埋込みを証明した。
  異なる次数型の等式は、次数の等式と同じ半群環代表であることから得る。
  degree0の定数単項式を使い、既存のk加群構造と積の整合性を証明する。
- 各次数の座標をDFinsuppでまとめ、Σₙ{v:order(v)=n}≃Sで添字を整理する。
  これにより全体のactual初期単項式が基底と分かる。
- 仮定：構造全体は可換係数環で構成。非零や積が消える条件の同値には非自明性を要求。
- 最終原稿：冪の同定→各次数の基底→全直和環→積、という証明順を採用できる。
  完備半群環との比較はこの構成とは別の未完定理として保持する。

## A16：単項式の核判定からactual核・像全体へ（Block10）

- Lean：`shiftExponent_injective`、`coordinateShift_ker`、`coordinateShift_range`、
  `xMultiply_coordinates`、`xKernelEquiv`、`xKernelBasis_eq_initial`。
- 数値作用は「liveな係数をv+mへ移し、deadな係数を消す」写像。
  v↦v+mが単射なので、異なるlive矢印の係数が同じ行き先で打ち消し合うことはない。
  従って核はterminal上に支持を持つ有限和の全体である。
- 像はincoming live矢印のある全座標の張る空間。逆包含はheadでない指数の実predecessorから証明する。
  全体の環のx乗算とこの係数作用が基底上で一致し、線型性で任意の元へ一致が延長する。
- actual接続は非自明な可換係数環を仮定する。核の線型同値と基底はactual初期単項式に一致する。
- 最終原稿：「Tの基底はdead矢印の始点」と述べる箇所に、単射性による無衝突の一文を補える。
  数値ラベルの単項式判定のみで核全体を済ませず、この線型性の段階を明示する。

## A17：head商をactual principal idealの環の商として同定（Block10）

- Lean：`headProjection_ker`、`actualHeadProjection_ker`、`xIdeal_eq_range`、
  `HeadAlgebra`、`headQuotientEquiv`、`headBasis_eq_initial`、`xMultiply_of`。
- head座標への係数制限は0拡張で全射、核は非head座標の支持空間、従ってactual x乗算の像に等しい。
  xGをIdeal.span{x}で定義し、そのk部分加群が乗算の像であることも証明した。
  こうしてAは単にhead空間と定義した対象ではなく、actual環Gのprincipal idealによる商となる。
- 非自明な可換係数環で、Aのhead基底と実単項式クラスが一致し、各headクラスは非零。
  全体のx作用と各次数のxActionも一致する。
- 最終原稿：Aの基底の主張を、制限写像の核・全射性とprincipal idealの像の同定で説明できる。
  N/Q、A全体の有限性、同jumpの加群同型や完備化比較はこの結果から無断で済ませない。
  global T≅Nの加群同型は導いていない。

## A18：非Apéry head空間をA全体のactual斉次イデアルへ（Block11）

- 原稿：V02 §2 / V03 O_COORDの非Apéry部分N。
- Lean：`nonAperySpace_mul`、`nonAperyIdeal`、`nonAperyIdealBasis_eq_initial`、`nonAperyIdeal_isHomogeneous`。
- 非Apéry head支持空間として出発し、Aの任意の元による乗算の閉包を証明した。
  和がApéryなら両因子もApéryなので、非Apéry項のlive積がApéryに戻ることはない。
  dead積は0。この単項式の性質をactual head基底の任意の係数の和へ延長する。
- Aの次数はactual G成分の像。係数フィルタとregistered gradingの射影が一致し、Nが各射影で保たれるので
  mathlibの `Ideal.IsHomogeneous` としても斉次性が成立する。
- 最終原稿：NはS₀の一部の変数だけでなく、A全体による乗算で閉じる、と明記できる。
  次数付き理想の存在を数値ラベルの定義だけで済ませていない。

## A19：実商Q=A/NとApéry基底・積（Block11）

- Lean：`AperyAlgebra`、`aperyProjection_ker`、`aperyProjection_surjective`、`aperyQuotientEquiv`、
  `aperyQuotientBasis_eq_initial`、`qMonomial_mul_ne_zero_iff`。
- Qはactual Aのactual ideal Nによる環の商として定義する。
  Apéry係数抽出の核がNで、0拡張により全射であることから、実商とApéry有限支持座標の同値を作る。
- 非Apéry指数のクラスは0、Apéry指数のクラスは非零。
  Qの単項式積が非零となる正確な条件は、orderが加法的かつ和がApéryであること。
- 仮定：非自明な可換係数環で成立する。特定の標数に依存しない。
- 最終原稿：Apéry空間をQの定義とするのではなく、実際の商から係数射影の第一同型定理で得る順にする。

## A20：actual quotientの次数・Hilbert関数・A₂との接続（Block11）

- Lean：`qDegree`、`mem_qDegree_coordinates`、`headDegree`、`lowDegreeQuotientEquiv`、
  `aperyAlgebra_finrank`、`qDegree_finrank`、`qDegree_high_sum`、`aperyGradedAlgebra`。
- QₙはGₙ→G→A→Qの実像として定義する。この像がorder=nのApéry支持空間と一致することを証明した。
  異なる次数の支持は交わらず、全体を張り、積は次数和に入る。AとQの両方でGradedAlgebraを登録する。
- 体kについてdimₖQ=m、q₀=1、q₁=e−1、q₂≤δ。
  高次総量はΣ_{2≤n≤δ+1}qₙ=δという有限のfiberwise計数で実装する。それより高い次数は0。
- actual Aₙ→Qₙは全nで全射。非Apéry headの次数≥3よりn≤2では核が0で、商写像そのものが同型となる。
  原稿のA₂=Q₂は自然な線型同型として読む。
- 最終原稿：数値Apéry計数（Block08）と、実商の次数への同定（本項）を区別して引用する。
  原稿のlength Q=mの数値に対応する総k次元を形式化済み。一般のModule.lengthという定義との同定は別途。

## A21：Qのactual原子による標準生成とArtin性（Block11）

- Lean：`apery_atomic_split`、`apery_atom_adjoin_top`、`apery_atom_generator_degree`、`aperyAlgebraArtinian`。
- 最長のApéry原子表示から先頭の一原子aを外し、残りvもApéryでorder(x)=order(a)+order(v)となることを示す。
  a≠mもApéry性から従う。従ってQでこの積はliveで、値による強帰納により全Apéry単項式が
  actual非multiplicity原子のクラスで生成される。
- 生成元クラスは次数1で非零。基底の線型結合からadjoinがQ全体となることを証明する。
  これは次数1生成を未証明の仮定として渡したものではない。
- 有限Apéry基底からModule.Finiteとdim Q=mを得て、mathlibの有限生成Artin加群の定理を適用しArtin環を登録する。
- 最終原稿：標準生成と有限性の両方をactual quotientの構成定理として明記できる。
  S₀からの多項式環表示そのもの、A・N・Tのすべての有限性、Torを済ませたとは扱わない。

## A22：νをactual Qの最高次数として構成（Block11）

- Lean：`qTopDegree`、`qTopDegree_realized`、`qDegree_ne_bot_iff`、`qTopDegree_le_deficit`。
- ν=max_{w∈Apéry}order(w)として有限集合から構成する。
  最大を実現するApéry元から原子を外す次数列を使い、0≤n≤νの各次数が存在すると証明する。
  実商の基底・次数の同定からQₙ≠0 ⇔ n≤ν。従って定義したνはactual Qの最高次数である。
- Block08の有限計数によるApéry order≤δ+1を接続しν≤δ+1を得る。
  原稿の「標準生成からν≤δ+1」を、実現する次数列とδ個の高次座標による直接計数に置換できる。
  標準生成自体もA21で別に証明するので、他の後続用途を失わない。
- 最終原稿：νの存在とactual性、上界をこの短い系列で説明できる。jump≤νの証明は本項に含まれない。

## A23：非x原子の単一S₀とactual作用・全射（Run12）

原稿：V02 §2 / V03 II.1 `O_COORD` の標準多項式作用。`NonXAtom` はactual最小生成元からmを除いた型で、変数の個数はe−1。
`polynomialToG` はその実初期単項式へ送るk代数準同型であり、Gへの全射とは主張しない。
T=ker(x:G→G)はGのannihilator ideal、NはAの実イデアルを通じて同じS₀の作用を受ける。
`polynomial_smul_G/T/A/N/Q` は実乗算との一致。`polynomialGtoA` / `polynomialAtoQ` は同じ作用で線型。
`polynomialToA_surjective` / `polynomialToQ_surjective` が全射である。

Aの生成性は、headの最長表示からliveな原子を一つ剥がす強帰納法で示した。
原子がmならlive incoming x-arrowとなりhead性に反するため、非x原子だけで生成される。
Qは自然商の全射から従う。この経路は一般的な多項式表示・Noetherian性を新たに仮定しない。
原稿には、S₀→Gの作用とS₀→A,Qの全射を区別し、次数1の実原子を明記する。

## A24：全terminalのjump上限を最長表示の切断で直接証明（Run12）

原稿：V03 O_COORDの `2≤jump≤ν`。旧方針のI_A⊆I_Q・生成次数・最小head経由の伝播を、同じ結論を持つ次の証明へ置換できる。
νはBlock11で構成したactual Qの最高次数 `qTopDegree`。τを任意のterminal、h=τ+m、d=ord(h)−ord(τ)とする。
d≥2はterminalの定義。ord(h)≤νならd≤νである。それ以外ではhの最長原子表示をν+1個で切り、h=u+v、ord(u)=ν+1、ord(v)=ord(h)−(ν+1)を得る。
uがApéry元ならord(u)≤νに反する。従ってu=y+m、y∈Sでありτ=y+v。
y=0ならu=mでord(u)=1となり、最長分解の次数とterminal不等式からd=1となる矛盾。
y>0ならord(y)≥1なのでord(τ)≥1+ord(v)=ord(h)−ν。従ってd≤ν。

Lean：`order_live_split`、`terminal_jump_upper`、`terminal_jump_bounds`。
最小headだけでなく、すべてのterminalを直接扱う。生成イデアル・Gröbner入力・体の標数の仮定は増やさない。
ν≤1ではterminalが存在せず、δ=0ではν≤δ+1=1よりactual T=N=0。
`xKernel_eq_bot_of_deficit_zero` / `nonAperyIdeal_eq_bot_of_deficit_zero` が実対象への接続。

## A25：反対向きfiltrationとactual同jump S₀加群同型（Run12）

原稿：V02 §2 / V03 O_COORD。同じS₀作用で、`descendingJump s` はTのjump≥sの支持部分、`ascendingJump s` はNのpredecessor jump≤sの支持部分。
数値集合だけではなく、実核・実イデアルの部分加群として構成した。
G/Aの任意の元による乗算で安定することを実単項式基底の有限和まで証明しており、S₀安定性はその帰結である。
`descendingJump_antitone` / `ascendingJump_monotone` は包含、`descendingJump_homogeneous` / `ascendingJump_homogeneous` はG/Aの実成分射影による斉次性。
D₂T=T、D_(ν+1)T=0、F₁N=0、F_νN=Nもactual部分加群の等式である。

商の分母は次/前の実部分加群をcomapして得る。`jumpStratumEquiv s hs` は実商同士のS₀線型同型で、hs:0<sの下で構成したので要求範囲2≤s≤νを含む。
証明は、同jumpの両端ラベルについてbase/headのlive条件が一致することから、actual乗算の係数行列が一致することを示す。
これをGの単項式基底から任意のG元へ、さらにS₀の任意多項式へ拡張する。
異jumpへの項は各商で消える。global T≅NのS₀線型同型は使用・主張しない。

`jumpStratumEquiv_degree` は同じ写像について、T側の次数pとN側の次数p+sの所属が同値であることを示す。
次数部分はG/Aの実斉次部分の逆像を取り、実商写像で送ったものとして定義した。
単項式の次数公式だけに留めず、任意の斉次有限和・商の元について成立する。

## A26：literal k[[S]]の実極大イデアル冪と係数条件（Run12）

原稿の形式級数環を、`PowerSeries k` のうちsupport⊆Sの部分k代数 `formalSeriesAlgebra` として直接定義した。
この選択ではAdicCompletionと形式級数の同定を別の仮定に置かない。
定数項写像のkernel `formalMaximalIdeal` は、任意の体で実極大イデアルであることを全射から証明した。
一般可換係数環ではkernelと冪を構成するが、極大性を主張する定理はFieldを仮定する。

`formalOrderIdeal_eq_pow` / `mem_formalMaximalIdeal_pow` が、無限級数についても実冪と「ord<nの全係数が0」を同定する。
正方向は積の係数とorderの超加法性。逆方向は、各vでord(v)≥nなら最長表示の次数nの接頭部u(v)を選ぶ。
ord(u)=nの集合はconductor boundにより有限。
同じ接頭部を持つ係数を形式級数g_uへ集めると、f=Σ_u t^u g_uとなる。
t^uは長さnの正元積なので実極大イデアルn乗に属する。
無限和の閉性や未証明の完備化定理を仮定せず、形式級数の係数を比較した有限和で逆包含を証明した。

## A27：代数的Gと完備半群環の接錐の次数付きk代数同値（Run12）

`FormalGradedPiece n` はliteral形式級数環の実極大イデアルn乗をn+1乗で割った商、`FormalTangentAlgebra` はその直和。
積は代表元の実積を商へ降ろして定義し、単位・k代数構造も構成した。
自然な `polynomialToFormal : k[S]→ₐ[k]k[[S]]` は同じ指数の係数を保存する。
各次数ではorder=nの有限切詰めで全射性、係数条件で単射性を得る。
`completedPieceEquiv` は自然な実冪の商の同値で、`completedPieceEquiv_mul` が乗法整合性。
`completedGradedAlgEquiv` はこれらを組み立てた次数を保つk代数同値である。

`completedGradedAlgEquiv_initial` / `_x` は実初期単項式・xの対応、`_xMultiply` は実乗算の可換性。
`completedKernelEquiv`、`completedHeadAlgEquiv`、`completedAperyAlgEquiv` と商写像の可換式によりG→A→Q・核を自然に運べる。
formal側Nはこの自然商同値でactual Nを移したイデアルであり、未証明の独立モデルとの同定を追加したものではない。
これで代数的Gを原稿の形式級数接錐として使う境界が閉じる。actual資源列・安定化・Tor/Betti・P14全体は後続Runの範囲である。

## A28：表示環の区別とactual最小表示（Run13・証明済み範囲）

非x原子のS₀=k[Xₐ:a≠m]と、全actual原子のe変数環PFを型で区別した。
`fullPolynomialToG_surjective` は実原子分解による全射、`atomDegreeOneEquiv` と
`fullPolynomialToG_linearForm_eq_zero_iff` は次数1の余分な線型関係がないことを示す。
`fullPolynomialToG_homogeneous` は全次数の斉次性を示す。
S₀→Gは一般には全射でないため、intrinsic source Bettiの環として使用しない。
`terminal_removeX_action` はactual Tでxが消えることからPF作用がS₀へfactorする証明である。
原稿では全e変数・非xのe−1変数・将来のcut r変数の三者を明記する。

## A29：具体的subset-recursion Koszulと通常Tor（Run13・部分閉鎖）

外積基底に対応する有限部分集合を、変数列の末尾からscalar coneを反復する形で実装した。
Kᵢ₊₁(x::xs;M)=Kᵢ(xs;M)⊕Kᵢ₊₁(xs;M)で、微分は(-d_old, X+d_old)の符号を持つ。
`koszul_cons_d_first` / `_second` が実微分のblock式、`koszul_d_squared` がd²=0。
`koszulH0Equiv` はH₀=M/(実変数作用)M、上次数はchain groupのIsZeroから消滅する。

新しい変数は処理済み変数idealの商で非零因子である。実変数idealのprime性と未所属から
`polynomial_variable_regular` を証明し、`scalarCone_exact_positive` のcycle chaseへ供給する。
`koszulResolution` は全変数列の実際の有限自由解消であり、augmentation exactnessの仮定は残らない。
`tensorKoszulIso` とこの解消から `torKoszulIso` を得る。
使用する通常Torはmathlibの「第二因子kを解消する」規約。TorをKoszulと命名して比較をrflにしたものではない。

未完：Tor比較のmodule-map自然性の可換式、第一因子を解消する規約とのbalancing、
実極小自由解消rankとの一致、graded Koszul/Tor。原稿でこれらを完了として引用しない。

## A30：無限k次元chain groupと有限homologyの分離（Run13）

`koszul_chain_finite` は有限**P**生成性、`koszul_homology_polynomial_finite` はNoetherian性によるker/im商の有限P生成性。
全変数のnull-homotopyを証明済みprojective resolutionから構成し、tensor同型でactual Koszulへ運ぶ。
`koszul_homology_action_reduction` はhomologyのP作用がaugmentationを通ることを示す。
これと有限P生成性から `koszul_homology_finite` が有限k次元性を与える。
M自体やchain groupの有限k次元性を要求しない。試験では1変数多項式環がk有限生成でないことも証明した。
`totalBetti` は有限P生成interfaceで定義し、通常Torへの係数線型同型と上次数消滅、自由Pの(1,0,…)を証明した。
graded Bettiの有限台・totalとの和はまだ未完である。

## A31：Run12比較のactual Tor運搬（Run13）

`completedPolynomialLinearEquiv` は全e変数PF作用について線型であり、
`completedTorIso` / `completed_totalBetti` が代数的Gと完成接錐を通常Tor/totalBettiで結ぶ。
同jumpについて `jumpStratumTorIso` / `jumpStratum_totalBetti` をS₀上で構成する。
Run12の元の実加群mapには次数差sがあるが、今回のTorは次数を忘れている。
このsをgraded homology/Torへ運ぶ証明は未完で、global T≅N加群同型は導入しない。

## A32：標準単項式と任意標数のminor（Run13）

`StandardExponent` はidealの**全非零要素**の初項から定義する。
除法によりnormal formの存在、初項矛盾で一意性を証明し、
`standardMonomialBasis` / `_apply` が実商の標準単項式基底を与える。
任意の候補生成元をGröbner基底と仮定する方法へ変更していない。
`nonzero_minor_rank_lower_bound` は列有限性を明示する。
整数det=±1のminorは任意体で非零であり、標数2でも同じ証明が成立する。
sourceのinitial ideal全体・block初項rank比較・harmonic本体は後続の実証明が必要。

## A33：局所rank式・flat複体比較の到達境界（Run13・未完を保持）

`homology_rank_correction` は短完全な実複体について
 dim Hᵢ(V)+rank δᵢ+rank δᵢ₊₁=dim Hᵢ(U)+dim Hᵢ(W) (i≥1)、
`homology_rank_correction_zero` はH₀についてincoming rankだけの式を証明する。
自然数の切捨て減算で補正を隠さない。Koszulが加群短完全列をこの実複体へ運ぶ接続、
部分Euler/syzygy・有界filtration比較は未完。

`fieldExtensionHomologyIso` は実L⊗ₖ複体のflat homology比較、
`extendedCoefficientKoszul_finrank` はactual Koszulを係数体へrestrictした複体の拡大の次元保存。
chain groupの有限次元性は使わない。L⊗ₖk[X]≃L[X]も証明済み。
ただし変更後L[X]加群のKoszulとの自然同型とactual G等のbase changeは未完なので、
これらをI_FIELD閉鎖・Betti体拡大保存の完成証明として引用しない。
形式級数環全体のtensor同型も使用しない。

## 最終照合時の手順

1. 各項目を最終原稿へ反映するか、元の証明へLeanを戻すかを確定し、対応する式番号を追記する。
2. 公開定理の仮定・添字・定義域・狭義/非狭義を原稿と照合する。
3. actual接続の未完欄を、証明済みの構成定理で埋める。
4. 最終Lean commitと原稿版のhashを固定する。現時点ではこの最終照合は未完である。

## A34 — Run13継続：実写像と短完全列

`koszulFunctor`のobjを実`koszulList`と定義的に一致させ、mapを同じ再帰的`koszulMap`へ整理。
coneの実inl/inr成分式、各次数の短完全列、connecting map、通常Tor比較の自然性、LESの三つのexactnessを追加。
数学的な微分や符号は変更しない。原稿には「実短完全列→実Koszul短完全複体→通常Tor LES」という接続を明記する。

## A35 — 極小自由解消rankの証明経路

一般Tor/Tor' balancingを未証明入力にしない。実minimal free towerの各syzygy coverの短完全列からdimension shiftingを反復し、H₀-inc=0を実極小性から証明してrank一致を得た。
`toProjectiveResolution`も実装した。原稿のrank橋はこのLES経路へ合わせる。極小解消の存在をこのrunで使う主張はない。

## A36 — gradingと無限chain group

内部次数tのchainは係数次数t−iの部分空間。実cone微分(-d,X+d)のhomogeneityを証明して制限し、d²は実d²から導く。
exactな無限直和のhomology比較から分解を得て、有限total Hから有限degree support/有限和を導く。
G/T/A/N/Qと同jump商には既存order次数を供給。同jumpはt→t+s、完備接錐は同次数を保持。
chainのk有限性を一般仮定にする文言は加えない。

## A37 — I_FIELDの実体化

L⊗ₖMに実L[X]作用を構成し、finite P生成、実Koszul複体比較、自然性、homology/total Betti保存を証明。
拡大gradingはL⊗ₖKₜとし、actual changed Koszulへのinclusionとhomologyの実直和分解を供給した。
actual G/T/A/N/Qとの係数変更は実指数基底の変数行列を比較して同定する。形式級数環全体のtensor同型は主張しない。

## A38 — rank Euler・有界比較・minor

部分交代和はℤで定義。実exact有限ベクトル複体のsyzygy像rankと一致し、非負・末端消滅を導く。
実monic filtrationのcokernel商homologyから有界比較を得る。後続のactual tower/cutへの実体化は別途供給する。
初項rank橋は実選択minorの三角性と±1対角から任意標数の下限を得る。harmonicの特定initial idealは後続担当。

## A39 — 数値受入と監査方法

残余体の二項係数Bettiは実零微分とchain基底次元から証明。
非零principal関係がaugmentation ideal内にある商のβ₀=β₁=1を実LESから証明し、P/(X²)と標数2に適用。
新規監査ではLean環境からconstructor/recursor/structure projection/生成補助宣言も列挙する。
途中版の証拠原本は`verification/block13/`とPARTIAL ZIPに凍結し、継続の証拠を別ディレクトリへ保存する。


## A40 — 独立レビュー後：actual L gradingの同定

拡大gradingの一般不変性だけでは、別途定義したactual L側のorder-gradingへの適用が明示されていなかった。
実指数degree fibreのscalar extensionを構成し、既存actual係数変更eとのinclusion可換式を証明。
同じtotal Koszul comparisonの実inl/inr式を使い、degree複体の同型とその可換式を導いた。
G/T/A/N/Qの独立したL側gradingへ適用し、actual graded Betti保存を明示的に証明した。
原稿のI_FIELDにはこのdegree同定を含める。標数2→RatFuncの五つのactual検査を追加した。

## A41 — Run14：least-offsetの表示を実半群元から構成

原稿§3の非x atom offset最小化に対し、Leanでは正の実半群元表示でまずbを最小化する。
そのbで最短の長さlを取り、最短表示のorder=l、全因子がactual atom、m因子を含まないことを証明。
`leastOffsetWord_exists`で原稿と同じ語を回収し、prefix最小性・剰余無反復・l<mを得る。
`order_stabilization`、`terminal_residue_sum`とA/N/Tの有限性をこのactual構成から導く。
最終原稿ではこの順序への変更が可能。鋭いδV上界のpath-countはまだ形式化していない。

## A42 — Run14：最大Q₂からSidonへの体非依存の橋

`degreeTwoPair`はactual degree-two Apéry元を非x atomのSym2へ単射する。
最大次元でcardが一致すれば全quadraticがliveで異なるApéry元を与える。
`maximal_low_pair_unique`で0を含む項と異次数の衝突も排除し、実AperyPairDataを作る。
任意標数・平方・even/composite mで成立。原稿A02の未実装橋はこの部分で閉鎖。
`actualCutRank_maximal`はr≥3の前提を保持し、Γ=<6,7,11>をr=2反例として記録する。

## A43 — Run14：同じactual Hの先行固定と未完境界

`jumpIdeal`は既存ascending supportをAの斉次idealにする。U_sの低次数同型は実商写像。
Hはactual U_sのdegree次元の和として固定し、有限台・H₀=δ・δ=0を証明。
`actualLayers`はhead=H₁、tail_j=H_{j+2}と全tail台を保持し、massの有限和同一性も証明。
Green、単一cut、truncated towerのP短完全列と単一次数生成、鋭い体積・区間cap・
head線形上界、actual Dataは未完。これらの未完を原稿の証明済み箇所の削除根拠にしない。
最終原稿とLeanの一致にはRUN14_REMAINING_DECLARATIONS_JA.mdの全接続が必要。

## A44 — Run14継続：鋭いoffset体積

原稿(3.1)の昇順添字を、leastOffsetの有限rank順列で表す。最短語のprefix最小性から
lρ≤rank(bρ)。初めてlevel n≥2へ達するprefixはactual非atom Apéry剰余を与えるため、
Lρ≤δ+1。両者からLρ−1≤min(δ,rank(bρ)−1)と全剰余の鋭いδVを証明する。
粗い安定化上界を体積予算へ代入しない。零剰余・m=1・δ=0も一般式に含む。

## A45 — Run14継続：任意標数のGreen次数2証明

対称双線型積μ:V×V→WがWを張る場合、最大乗算rank Rに対してdim W≤choose(R+1,2)を証明。
実際のminor多項式でgeneric独立性と最大rank pencilの核像性を示す。
全平方が零なら交代積のchoose(R,2)計数を使い、そうでなければ最大rankかつ非等方の点を
非零二次多項式の回避で選ぶ。2で割らず、標数2を含む。
その一段評価を同じV内の独立なflagへ反復し、全prefixで原稿X_GREENと同じ上界を得る。
引用や未証明Green入力は追加しない。原稿ではこの実証明を次数2特殊版の独立な補論として採用可能。

## A46 — Run14継続：一つのactual cutとP

actual A₁×A₁→A₂の積が全A₂を張ることをlive分解から示し、Green flagを適用。
r=max(2,p)へ独立形式を補完し、同一cutの二次積spanがA₂全体になる強いwitnessを得る。
高次消滅・各次数の生成写像とも、この同じwitnessから証明する。
一次形式はS₀へ実係数座標で持ち上げ、その線型独立性を証明。Pはr変数の形式的多項式環とし、
実G/T/A/N/Q・jump層・towerのS₀作用を一つの写像P→S₀で制限する。
A内の像が代数的独立であるという仮定は置かない。
有限体では既存の同標数k(X)上にcutを構成。Run13のactual graded/total Betti保存を引き続き利用できる。

## A47 — Run14継続：actual towerと極小生成元

F_sは既存actual jump ideal、U_s=A/F_(s−1)。actual order座標の支持≥nをイデアル化し、
その実像からX_s、M_sを構成する。F_sの像K_sはRun12のascendingJump商とS₀線型に同型。
terminalの正次数を用いてK_s⊂M_sを証明し、実商写像で短完全列を構成する。
同一Pへ制限した全写像の単射・完全性・全射とX_(ν+1)=0を証明。
cutの強い二次spanからA_n→A_(n+1)、U_sの次数間の全射を構成し、X/Mの単一次数生成を得る。
Pの変数倍部分がちょうど次の次数以上のtruncationに一致すること、augmentation商が
actual底次数とk線型同型になることも証明し、極小生成元数を実次数のfinrankと同定する。

## A48 — Run14継続：一意なHの全資源と数値閉鎖

U_sの実基底は、F_(s−1)で消えないactual headラベル。Apéry headとterminal successorを分離すると、
H_tは原稿の区間[0,sρ−2]と[p,p+d−2]の個数に一致する。
同剰余で二つが同時に寄与すると、後のheadの前駆orderが先のheadのorder以上となり矛盾する。
これにより全tでH_t≤m−1。全区間長を加え、terminal_residue_sumを使って
Σ_t H_t=Σ_ρ(Lρ−1)≤δVを得る。tailはscalar cutoffで切り捨てない。
H₁+a=δ+ell、ell≤e−1、同cutの次数生成からH₁≤rδを証明。
r≥3に限って三角数head capを得る。r=2の<6,7,11>へこの系を適用しない。
Hの体非依存性を実基底cardから示し、有限体にも同じ資源評価を運ぶ。
`actualNumericalDataWithCut`/`ActualWitness.numericalData`はこの実Hと同一cutを使用し、
actual Sidon境界と併せて既存`all_rows`へ接続する。

## A49 — Run14の認証境界とRun15

歴史的`audit/run14/RemainingGoals.lean`の5命題は改変せず、継続監査用ClosedGoalsで全て証明する。
Green/cut、offset、tower、資源、SidonのRun14接続と、actual Torからの行上界、target Bettiの同定は区別する。
後二者とordinaryのactual Betti閉鎖はユーザー指定どおりRun15。Run14の数値行比較を最終P14定理とは呼ばない。
旧PARTIALの検証原本・ZIP・固定環境を保持し、継続の全生成宣言の公理と明示型は別証拠へ圧縮保存する。

## A50 — Run15部分実装：P/R/全表示と同じcutの座標

r変数P、r+1変数R、e変数全表示を型で区別する。
原稿の「基底へ延長」はspan包含だけでなく、各λが元の位置に残るprefix延長として証明した。
P→S₀のsplit単射、R→全表示のsplit単射を実多項式写像で与える。
PのA像の独立性は使わない。GのR有限性はfiniteHeadExponentの実head生成とx作用から示す。
GのP有限・k有限を仮定しない。変数変更によるTor保存はまだ未実装。

## A51 — Run15部分実装：actual Eulerと第2/3Tor鎖

c_jは指定した環の通常Tor/Bettiの整数部分交代和として定義する。
実LESからconnecting rankとその補数を区別し、H₀を含む二つの恒等式を証明。
有限k次元層だけでKoszul鎖の次元を使い、c_j=choose(r−1,j)length−rank d_(j+1)とc_r=0を得る。
自由Pのc_1=−1も保持し、無条件のEuler非負性へ一般化しない。
同じPの実towerに第3Tor不等式を適用し、実descending jump filtrationと同jump同型から
第2Tor不等式を証明した。global T≅Nやconnecting map消滅は用いない。
第1のx-Koszul比較・harmonic適用・actual row閉鎖は未完。

## A52 — Run15部分実装：一般APの標準指数

一般公差d≥1を保ち、AP membershipをx=l*m+j*d、j≤v*lで表す。
この数値witnessが実際に長さlの正の原子分解を与えることを証明する。
jをmで正規化するとm係数がq*dだけ増え、標準指数i<mの係数がactual orderになる。
これによりApéry元ceil(i/v)m+i*d、order(x+m)=order(x)+1、actual coneのx正則性を得る。
原稿では公刊Betti入力とは分離した補題として採用可能。GSS解消・APのBetti一致は未形式化。

## A53 — Run15部分実装：actual intervalと数値畳み込み

actual最大原子Mからw=M−mを定義し、生成区間[m,M]のadditive closureが
v=min(w,m−1)、d=1の真正APと一致することを証明する。2m以上の冗長原子は実加法閉包で除く。
wide時のtarget carrierは{0}∪[m,∞)、最小原子数mになる。
Vandermondeと既存target_stepから、target差の正確な係数畳み込みを既存R_jへ接続し、
T_(f+2)−T_(f+1)のH₀補正係数も証明する。これはactual target Betti同定の代用ではない。

## A54 — Run15の未完境界

23新規数学moduleの部分実装があるが、ordinaryのactual Betti閉鎖は未完。
初期「加群」の標準基底と実minor、一般APの実解消、H₀作用を保った全変数への比較を
未証明入力やconstructorのfieldとして追加しない。
監査用RemainingGoalsの8命題はdef : Propとして保存し、productionへ依存させない。
最終原稿との一致にはRUN15_REMAINING_DECLARATIONS_JA.mdの接続が必要。

## A55 — Run15継続：actual加群からのharmonic評価

任意個数のP生成元に対し、加群項m.syn ×lex Fin qからactual標準基底を構成し、除数閉性と乗法の三角性を証明した。実Koszul微分に入れる列と実座標から読み取る行で三角小行列を作り、対角±1を証明する。有理数での多重次数平均化と外積部分集合の計数により実boundary rankを評価し、有限鎖Eulerと接続した。Harmonic.harmonic_boundは元のHarmonicGoalそのものを証明する。体内で分母を割らず、標数2も保持する。原稿では初項複体全体のrank比較を独立の入力とする代わりに、この直接の実minor証明を採用できる。

## A56 — Run15継続：同じcutのtower資源row

実truncationの座標から次数分解・単一次数生成・有限台を構成し、H0を実最下次数成分へ同定する。末端Xの消滅を実商から証明して第2/3Tor不等式をtelescopingし、同じH_tだけの既存rowへ全行を接続した。TowerRow.cutTower_resource_rowはj=1とj=rを保持する。actual Gからの第1x-Koszul比較、B評価、補正済み全変数比較と一般AP/targetのactual Bettiは引き続き接続が必要であり、ordinary枝の完成はまだ主張しない。

## A57 — Run15継続：actual x比較と相対Rの末端行

actual Gの加群として0→T→G→xG→0および0→xG→G→Aを構成し、同じcutのRへ制限して実Koszul複体へ送った。二つの完全列の写像錐を比較する実完全列から、有限なのはT/A側のhomologyだけで足りるEuler不等式を証明した。変数順none::some λの実自由Koszul解消と通常Torの比較を経て、`ActualWitness.relative_Euler_le` は全jについて c_(j+1)^R(G)≤c_(j+1)^P(A)+c_j^P(T) を与える。GをP有限または係数体有限とはしていない。

同じ完全列の等式には実connecting rankの減算を残す。末端でA側homologyの実台が切れるためそのrankが0となり、有限長P加群のEuler末端と合わせて`ActualWitness.relative_Euler_terminal` によりc_(r+1)^R(G)=0を得た。c_r^R(G)=0への強化はしていない。元の`RelativeTerminalGoal`そのものの証明は`audit/run15_xclosure/ClosedGoals.lean`。原稿では、未構成のスペクトル系列退化を置く代わりに、この二つの写像錐と実connecting mapによる十分な比較を採用可能。

## A58 — Run15継続：first-order加群の実boundary rankとB計算の準備

各変数が定数射影を通じて独立な一次ベクトルへ作用する有限加群について、実slot分解によるrank上界と、各外積から一つの変数を除いて選ぶ実±1対角minorによるrank下界を一致させた。`SquareZeroEuler.squareZero_bettiEuler` は c_j=length·choose(r−1,j)−choose(r,j+1) を与える。実モデルは自明二乗零拡大 k⊕k^(r+f) とP=L[λ]の具体的aeval作用であり、f個の余分な一次生成元も保持する。H0はf+1で、標数2の非零boundary・第1行・topを検査する。これはactual Bとの同定を自動的に証明しない。同定後に長さeを代入しPascal恒等式で既存L_jへ接続するための共通補題として原稿に追記可能。

## A59 — Run15継続：actual Bの評価と実Tor資源rowの閉鎖

actual B=A/highIdeal(2)の基底とlambda作用を実商から構成し、BのEuler値を既存L_jへ一致させた。同じcutのhighIdeal(2)とX2の実同型、B短完全列、actual x比較、同じtowerと同じH_tから、`ActualWitness.actualTor_resource_row`により全1≤j≤rのactual R-Tor-to-rowを証明した。`actualTor_target_row`はそのままRun14の数値全行定理へ通す。元のActualTorToRowGoalそのものの証明はaudit/run15_bclosure/ClosedGoals.lean。原稿では83組等の再計算を挟まず、既存数値定理へこのactual接続を明示できる。

## A60 — Run15継続：B全作用とnative H0候補の残余Z加群

actual Bの二乗零代数同型を同じextendedHeadBasisで構成し、lambdaだけでなく補完Zを含む全non-x作用を一致させた。さらにA/(lambda)の実代数商とk⊕k^fを同定し、残余Z作用を保持した実加群同型から通常Bettiの第0行1、全正行i*choose(f+1,i+1)を証明した。原稿のH0同定を支えるnative商の計算として採用できる。ただしactual R-Koszul H0とのZ作用を保つ同定と、補正済み全変数の有界比較は別の未完義務である。この計算のみをO14完成としない。

## A61 — Run15継続：actual R-Koszul H0の残余作用

実要素x/lambdaのnative G-linear Koszul複体を構成し、既存の相対R-variable Koszulとの実複体同型を証明した。native境界イデアルをideal(x,lambda)として計算し、headへの射影と既存cut idealを介して、H0を残余Z作用を保持した二乗零モデルへ同定した。`nativeCutH0ZIso`と`nativeCutH0Z_betti`は実際の誘導作用の同型と全行の通常Z-Bettiを与える。単なる長さf+1の同定で置き換えていない。

## A62 — Run15継続：第0項の補正を保持する実有界比較

任意native complex Kについて、K→single0(H0 K)の実全射とkernelの実短完全列を構成した。kernelのH0=0、正次数homologyはKのものと実同型である。追加変数の写像錐は実完全列からhomologyの有限性と二項係数上界を導き、H0側を別に保つ補正済み比較を証明した。`ActualWitness.nativeFull_corrected_bound`はこれを同じactual x/cut/Zへ適用し、H0モデルとactual relative R-Bettiを代入する。無限次元のchain groupにfinrank加法性を使わず、有限なのは必要なhomologyだけである。原稿では未構成のスペクトル系列の退化の代わりにこの有界比較を採用できる。

この段階の左辺は実全変数作用のnative複体のhomologyである。元の最小表示のintrinsic full Torとの線型変数変換比較は引き続き別の未完義務であり、元のCorrectedFullTransferGoalが閉じたとはまだ表示しない。一般APの実Betti/環・接錐Betti一致、actual target、元体への最終下降も残る。

## A63 — Run15継続：全最小表示の変数変換と通常Tor保存

環同値で実射影解消を運び、tensorの実自然同型とhomology保存を用いて通常Torの同型を構成した。augmentationを保つ多項式環同値と線型変数変換に適用し、有限生成の伝播と通常totalBetti保存を得た。同じcutの拡張non-x基底をactual xと合わせ、全e変数の実多項式環同値を構成した。補完Z、x、lambdaの順の変数列は完全かつ重複なしであり、実作用の一致からnative全変数複体を通常intrinsic Torへ同定した。AlgEquivだけからTor保存を主張していない。

## A64 — Run15継続：元の補正済み全変数比較を閉鎖

actual H0作用と実有界比較へ全変数Tor同定を接続し、`ActualWitness.correctedFullTransfer`により元のCorrectedFullTransferGoalそのものを証明した。H0項f+1は正Betti列の和をj=1から始めることで除外され、対象は元の全e変数の最小表示である。f=0/非零f、標数2の非自明shear、全行で通常Tor保存を受入検査する。補正済み比較を単なる係数恒等式として置いていない。

## A65 — Run15継続：任意元体・全正行のordinary数値容量

相対Rの実H0からbeta0=f+1を証明し、相対末端c_(r+1)=0と通常Torの上次数消滅から全j>rのc_j=0を得た。既存数値rowsに、余ったj>rのtarget非負性を加えて全正行を保持する。beta_j=c_j+c_(j-1)の正確な係数畳み込み、第0項の補正、既存target差恒等式を合成して、`ordinary_betti_bound`は任意元体k・e>=3・全i>=1でactual source beta_i<=i*choose(m,i+1)を与える。体拡大は通常Betti保存により元のkへ下降する。

この数値容量の証明自体は幅仮定を使わず、原稿のordinary枝に必要なものより強いsource上界となる。literal interval completionがordinary targetである同定と、actual targetのBetti公式は依然必要である。一般APの公差d>=1の実Betti公式と半群環/接錐Betti一致も残る。Run15全体の完了とは表示しない。

## A66 — Run15継続：正則xの実縮約とactual ordinary target

実正則元rについてR --r→ R →R/(r)の実短完全列を構成し、native Koszulへ送った。単射の写像錐のhomologyと商複体のhomologyの実同型から、x正則なactual Gのintrinsic全変数Torを、非x変数によるactual A=G/(x)の通常Torへ同定した。有限次元chainやスペクトル系列の退化は仮定しない。

APのv=m−1では、一般公差d>=1を保ったApéryリストから全headのorder<=1、高次数ideal(2)=0を証明した。actual non-x作用と実一次基底の独立性、実signed-unit boundary rankから全通常Bettiを計算し、第0行1、正行i*choose(m,i+1)を得た。literal interval completionへ実際に代入し、完成接錐との通常Tor比較も適用した。二変数targetも扱い、r=2 cutを過大適用していない。

## A67 — Run15継続：第0行の等式とordinary actual閉鎖

実多項式表示の全射とactual augmentationをP加群の全射として構成した。H0の右完全性を実Koszul写像から証明し、free Pと実residue moduleの第0Bettiが1であることの間にactual sourceを挟むことで、任意sourceと完成接錐の第0Betti=1を証明した。Gの係数体有限性は使わない。sourceとtarget双方の第0行を等式として保持する。

`Ordinary.ordinary_actual_completion_betti_le`は任意元体・全行で、actual完成sourceとliteral interval completionのactual完成targetを各自の最小表示で比較する。元のOrdinaryActualCompletionGoalそのものの証明はaudit/run15_ordinary/ClosedGoals.lean。Gamma<6,7,11>のrank2例、Run12のterminal26/41とjumpの異なるchanging例、標数2、m=2 target、一般d>1のAP特殊例を受入に含めた。

一般APの代数的半群環Betti公式と、一般APの半群環/接錐Betti一致はまだ未完。v=1やv=m−1のcone公式だけで公刊共通入力全体を閉じたとは表示しない。

### A68 — 一般APの代数半群環と接錐のBetti一致

ArithmeticSequence.ConeBetti.semigroup_cone_totalBetti。公差d>=1、m>=2、1<=v<m、gcd(m,d)=1、任意体・全行。実(t^m)商とactual HeadAlgebraのAlgEquivを構成し、両者の実非x変数作用が一致することを証明した。代数的半群環のt^m正則性は係数の平行移動で証明、接錐のx正則性は既存のactual核座標証明を使用。実Koszul正則縮約から各自の最小全原子表示における通常Tor/Bettiの一致を得た。環本体同士の同型や未証明の標準基底を仮定しない。

APの和がApéryに残る場合のorder加法性が商AlgHomの核心。canonical表現のindex和がm以上ならm前元を明示構成して矛盾させる。index和がm未満ならcanonical_orderを直接適用。原稿X_AP_CONEの十分な別証明として残せる。一般AP数値公式X_AP_BETTIはこの比較だけでは閉じず、継続する。

### A69 — 一般AP公式への別経路：actual ordinary補助coneと実kernel

ordinaryModel、HeadIndex、ModelCoordinates/Multiplication/Quotient/Kernel、ModelKernelShift/NativeWindow、WindowArithmetic、ModelWindowAction。v>=2に対して実Gamma=<v,...,2v−1>の接錐Bからactual AP head Aへ全射AlgHomを構成。kernel Jは実核、添字>=mの基底を持ち、actual x作用がvだけ添字をずらす。actual R-module J/xJは長さv、D=v−((m−1)%v)により二次数に分かれる。各変数作用とactual native正則縮約を証明した。BやJのk有限性は使わない。

これは一般公式X_AP_BETTIの完成証明ではなく、同じrun内の実接続用構成。J→BのTor写像消滅、最小表示の同定、実二次数作用への変数変換と最終LES合成は別途証明する。

### A70 — 評価点によるKoszul境界rankと二次数加群の全Betti公式

VandermondeSpark、KoszulIncidence/MomentRank、CoefficientSlotsEquiv、TwoStepSlots/Boundary/Betti、EvaluationVariables。任意標数、distinct pointsの存在する体上で、実variable actionがu(t)*ell(t)の二次数加群の境界をactual recursive Koszul signsで評価。p>=Dで単射、p<=Dで全射となる。actual境界はsurjective lower projection、moment map、injective upper inclusionに因数分解される。range finrankを同定して全行beta_iを計算し、beta0とtopも保持。

この線型代数的補題は一般APの実作用へ適用するまで、AP公式の証明として数えない。同標数無限拡大から元体への帰還は既存actualG Betti保存で行う。原稿の最小解消の別経路となる候補だが、未完成のLES接続を「退化」として仮定しない。

### A71 — 一般AP公式のactual接続とx因数分解

A69–A70の候補を実APへ適用して完成した。ModelVariableOrder/ModelPolynomialBetti/ModelKernelBetti/ModelHeadBettiは実最小表示とnative正則縮約を接続し、WindowHankel/WindowBettiはactual J/xJ作用を座標反転と実Vandermonde変数変更で評価作用へ移す。JはP有限生成、BもP有限生成だが、いずれもk有限次元とは扱わない。

ModelKernelDivision/ModelTorClosureではm>vから実J⊂xBを証明する。xの単射性で作る実B線型の除算写像により、実包含J→Bを多項式変数xの倍として因数分解する。KoszulVariableMapsの実null-homotopyと実LESから全行のBetti加法を得る。過去の候補「gradingからTor写像消滅」を置換し、そのgrading集中まで証明したとは主張しない。GSSの解消自体ではなく、同じquotient Betti結論の独立なactual Koszul証明である。

BettiFormula.semigroup_totalBetti/cone_totalBetti/completed_AP_totalBettiは一般公差d≥1・元の任意体・0行を含む全行に適用できる。無限拡大上で計算した実cone Bettiを体拡大保存で元体へ戻す。ProfileBoundsは1≤b≤vのm=av+b、D=v−b+1、i>vの0、Fmin下界と幅方向単調性を保持する。WidthとIntervalAPBettiは実幅、literal targetの実最小表示と完成接錐のBettiへ接続する。v=1、D=1/v、i=D/D+1、0/top/top+1、標数2、d>1を受入に含めた。

### A72 — Run15の元の8目標の同時閉鎖

audit/run15_closure/ClosedGoals.leanのall_original_goals_closedは、凍結した元の8目標の型を変えずに連言を証明する。A54以降の過去時点の未完記録は履歴として残すが、Run15内の数学的未完は解消した。ordinary全行比較はe≥3、幅w≥m−1、元の任意体、literal完成source/target、各自の最小全変数表示。一般AP公式と狭幅targetの計算を証明したことは、狭幅sourceとの主比較を証明したことを意味しない。後続Run16–20の完成条件は保持する。

### A73 — TLOW個別行の明示的export

APLowerRowsは一般Fminから、F1≥choose(v,2)+1、F2≥2choose(v,3)+v (v≥3)、F3≥3choose(v,4)+choose(v,2) (v≥5)、F4≥4choose(v,5)を証明し、同一literal interval completionの完成接錐へ一括適用する。v=3/5の隣接二項係数が等しい端点も含む。一般下界が存在するだけで個別行まで供給済みとはせず、この接続を明記する。


### A74 — Run16の同じactual sourceのEH正規化と整数core

raw EHのm,d,a,uを維持し、actual sourceの最小原子、multiplicity、embedding、widthを証明。du<mやgcd(m,u)=1は追加しない。狭幅では元のcarrier・次数付き代数・完備接錐・各自の最小表示のBettiへ戻る。整数対(n,B)の実coreからGへの全射と全長い表示による核、E上のC≃⊕M、G≃⊕M/(M∩T)を実作用で構成した。

### A75 — 全競合停止、実端点socleと同じ向きの資源

極小core点の純内部語長<u、全残基非空、周期u/gcd(m,u)を用いて全jを停止。実端点homologyは(PG,PG+R,R)。Gのk有限性を仮定しない。実socle基底をM内のNの角と同定し、隣接極小点の角式も証明。T商への実単射からR≤Σz≤W−uとR≤u max(Hx−2,0)を得る。PCとPG、Rと内部σを混同しない。

### A76 — 一般Artin評価の証明経路変更

真の斉次ideal・一次関係0・実有限商を持つ任意体上のT/Iについて、実Gröbner正規形が次数を保つこと、実基底・有限台・Hilbert総和・次数0生成とaugmentationを構成。第一行はRun15の実標準加群の調和型定理j=1から導出し、parent/child計数の重複を避けた。実完全列のconnecting mapからb1=実idealのTor0を供給。三形、負係数を保つ符号付き差、q5の差14をℚ上で証明。独立な±1 Koszul minorにより全正次数評価を得る。詳細と判断の費用はRun16原稿対応台帳・execution ledgerに記録。

### A77 — Run16の全行・二内部変数・具体例

実QC→QGの核完全列でPC−PGを補償し、q内部変数からq+2全変数へ移行。floor・減算の加法形、第0/top/上次数行を保持し、元の狭幅完備sourceへの全行APIを構成した。q2のみ実単項式核を証明。内部carry作用と内部socle点基底からσ_Cを数え、実二変数Koszulから(1,σ_C+1,σ_C)と四行を得る。一般qの非単項式関係を排除しない。

三例のactual(PC,PG,R)=(5,4,0),(5,5,0),(9,6,1)は任意体でLean等式。これらは実対象との一致を証明した有限計算を使う。反射でHxが異なること、q3の生存関係、標数2を確認する。799例の独立回帰は一般証明の代替ではない。Run17–20の担当は引き続き保持する。

## Run17 alignment

Kneser uses the source-checked Bakšys–Dillies implementation of the DeVos proof, with attribution/license.
SC uses a proved positional connected-subsequence argument following Lev; a direct sharp-term uniqueness lemma removes the need for the cited coset-structure proof.
The original SC conclusion is proved without extra assumptions. Actual D.u, a_i, W and QC are retained.
See [Run17 paper ledger](RUN17_PAPER_CORRESPONDENCE_JA.md) for all exports and the manuscript changes to preserve.

## Run18 PARTIAL：疎幅一IDの閉鎖

V03 W_SPARSE / V02 §13.4 W17–W21をactual source/targetの全行へ接続した。`NSP14.Run18.sparse_closed`が凍結契約を証明する。Run18全体は未完であり、X_BHP_EK・W_EDGE・W_DENSE・W_FIVE・W_CLOSEはopenのまま。詳細・範囲・原稿との差は`docs/RUN18_PAPER_CORRESPONDENCE_JA.md`、検証は新規排他的ディレクトリ`verification/run18/runs/`を参照。

2026-11-15 Run18 R09：Pardueのdistractionに必要な実多項式線形同型・実monomial ideal像のideal性・全Hilbert関数保存をgeneric coefficient field上で構成。原典のBetti保存やlex停止を引用だけで形式証明済みと数えない。元のgraded EK conjunctと実initial Betti比較は既証明、assigned三IDのみ閉鎖。R09 cold/独立レビューはabf2dad sourceの新規六moduleを含む範囲で成功し、一般BHP・lex存在・dense/globalの未完は維持。

2026-11-15 Run18 R10：Pardueのgeneric distraction段階に対し、引用を仮定にすることなく実Koszul chain同型から全graded Betti保存を構成。原典の極化/正則切断の代わりに、実selected coefficient matrixの指数依存外積変換と実収縮の可換性を証明した。scopeはGenericDistractionField上の実monomial ideal。任意の元の基礎体idealへの接続・lexへの反復と停止・lex存在・dense/globalは未完。cold全回帰と独立レビューは6bcd0259b84b61614d3e6f5ed14f30aa935717e2までの実装を認証し、Run18全体の完了ではない。
