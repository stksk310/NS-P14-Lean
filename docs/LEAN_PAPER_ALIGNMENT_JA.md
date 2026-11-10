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

## 最終照合時の手順

1. 各項目を最終原稿へ反映するか、元の証明へLeanを戻すかを確定し、対応する式番号を追記する。
2. 公開定理の仮定・添字・定義域・狭義/非狭義を原稿と照合する。
3. actual接続の未完欄を、証明済みの構成定理で埋める。
4. 最終Lean commitと原稿版のhashを固定する。現時点ではこの最終照合は未完である。
