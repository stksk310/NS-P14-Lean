# V05→V06：具体的な端点周期停止を主依存から外す

本番読解基準commit：`345e2d82fea50ef89e00a8f35c4fb53ac601d7ce`。
保存したV05端点章のSHA256：`87e6e9835ef1bb425a4924a5c0d0e22a837b2a43254dc770c866a674cb175aba`。
採用したV06端点章のSHA256：`875ec4dc43c567391d37b37924fc89437ebd169a989f5933fc3d6a08b99cab9f`。
V04/V05、本番Lean、凍結命題、既存証跡は変更していない。

## 1　不要にした強さと、残す全称性

旧E-STOPは、全競合イデアルT_sを具体的な有限個の競合長jに切り詰める**計算可能な停止回数**を与えていた。
主比較に必要なのは、全jから定義したT_sの極小点を有限個の角として並べられること、
その第一座標がH=max(Hx−2,0)以下であること、各T_sに純v冪があることだけである。
V06ではこの三点を直接証明する。停止回数そのものを別の必須付録へ移したわけではない。

全長い表示の必要十分条件(E-5)、全jの禁止始点(E-6)、
実核N_s=M_s∩T_sと元のGの商表示(E-7)は**全文byte一致で保持**した。
「有限個のjだけを経験的に調べたので核を得た」という弱い主張へ置き換えてはいない。

## 2　新しい補題E-HEIGHTの正確なstatement

EHを固定し、0≤r,s<u、epsilon_r=[r>0]、r+jm=s+cu、j≥1とする。
長い側の極小点(L,K)∈Min M_rからの全ての始点

\[
 (A,B)=\bigl(\max(0,L-jd-c+\epsilon_r-\epsilon_s),K+c\bigr)
\]

について次が成立する。

1. `c-epsilon_r+epsilon_s=ceil((r+jm)/u)-ceil(r/u)>=floor(jm/u)>=j`。
2. `A<=max(Hx-2j,0)<=H=max(Hx-2,0)`。
3. 各固定sについて、全jからの始点に現れる各第一座標Aごとに
   `b_A=min{B:(A,B)は始点}` を取ると、
   `T_s=(x^A*v^(b_A):Aが現れる)`。生成元数は高々H+1。
4. 各固定sに対し、あるj≥1とあるr、(L,K)∈Min M_rから第一座標0の始点が得られ、
   T_sは純v冪を含む。

このstatementは旧周期停止回数を仮定せず、gcd(m,u)=1も仮定しない。
主証明に必要な有限性を得るための新しいNoetherian定理は導入していない。

## 3　証明と境界

`ceil(r/u)=epsilon_r`、`ceil(s/u)=epsilon_s` とr+jm=s+cuから、1の等号はr=0やs=0を含めて成立する。
jm=hu+t、0≤t<uと書けば

\[
 \left\lceil\frac{r+jm}{u}\right\rceil
 =h+\left\lceil\frac{r+t}{u}\right\rceil
 \ge h+\left\lceil\frac r u\right\rceil.
\]

これでcarry五場合の表を使わずに1を得る。m>uよりfloor(jm/u)≥j、d≥1よりjd≥j、
L≤Hxを始点の整数式に代入すれば2を得る。clampはこの整数差を評価した後に取る。

3では、各非空な第二座標集合が自然数の部分集合なので最小値b_Aを持つ。
同じ第一座標Aの他の始点は(A,b_A)に座標ごとに支配される。
可能なAは0,…,Hの有限集合だから、全jにわたる生成イデアルがこの有限集合で生成される。
特にT_sの極小点はこの有限生成元の部分集合で、第一座標はH以下である。
これは二変数環一般のNoetherian性の再証明ではなく、今回の有界な始点に必要な一段の議論である。

4ではsを固定して2j≥Hxとなるj≥1を取り、rを**整数差**s−jmのmod u代表とする。
M_r≠0はE-FIBERで既証明なので、その極小点を選べる。2によってA=0となり、
B=K+c≥1なのでv^B∈T_sを得る。rをjから選び直すだけであり、jmの乗法逆元は使わない。
従ってgcd(m,u)>1にもそのまま適用できる。
Hx≤2では全始点の第一座標が0となるためT_sは純v冪の主イデアルとなり、
後続の角数z_s=0、実socle単射から元のR=0が従う。

## 4　後続で保持した接続

E-RESOURCESは、有限生成・純v冪をE-HEIGHTから受け取り、
T_sの極小点を第一座標増加・第二座標減少に並べる。
隣接角によるsocle基底、`z_s<=A+B-kappa_s`、carry総和の相殺、
`R<=min(W-u,u*max(Hx-2,0))` は従来のままである。
E-TOR以降はV05と全文byte一致し、以下を保持する。

- 実核N=M∩T、PCとPGの区別、QC→QGの核の長さPC−PGによるTor補償。
- 固定した元の向きのHxとactual R。反射やunitで別sourceへ置き換えない。
- 全q、i=0、top i=q+2、その上の消滅を含む全行。
- 任意標数の符号付き単位minor、有理重みの数値計数。
- E-ARTINのsigned評価・q=5の差14を含む、今回scope外の本文。

幅4は別章N7が自由・制限anchorと全jを独立に尽くしており、
その二座標条件・実像独立性・全multiplicity表を変更していない。
旧E-STOPを除去したことを、幅4の全競合解析を省く理由にはしていない。

## 5　Lean対応と形式化境界

|役割|対応する既存export・保存先|今回の状態|
|---|---|---|
|全jの実競合・実核|`NSP14.Endpoint.Data.actual_dead_iff_forbidden`, `.actualDeadFiber_eq_inter`, `.actualFiberModuleEquiv`|既存紙上・形式化結果を保持|
|carry差の下界|`NSP14.Endpoint.Data.carry_epsilon_lower`|同じ下界の個別結論は形式化済み。新しいceiling恒等式経由の紙上routeは新規exportなし|
|floor≥j・全j高さ上界|`NSP14.Endpoint.Data.floor_jm_ge`, `.forbiddenStart_height`|個別結論は形式化済み|
|有界第一座標ごとの第二座標最小によるT_s有限生成|新規named exportなし|紙上証明済み・新route未形式化|
|固定s・十分大jとr=(s−jm mod u)から純v冪を得るconsumer|新規named exportなし|紙上証明済み・新route未形式化|
|極小点の高さとRの上界|`NSP14.Endpoint.Data.competitorMin_height`, `.actualR_le_height`, `.actualR_le_Rhat`|同じ結論は既存形式化済み。ただし本番の`competitorMin_height`は旧停止を経由し、新紙上routeへ置換していない|
|旧明示的周期停止|`NSP14/Endpoint/Stopping.lean` の `.competitorFiber_stopping`、保存したV04/V05本文|旧結果を保持。本稿主証明と必須付録からは要求しない|

後で新routeを形式化するための入力は、全jの競合定義、極小長い側点の存在と高さ、
始点の単調性、および上の1–4のstatementである。
本番のimport graphからStoppingを取り除いた、既存consumerの推移依存を軽くした、
新routeのLean検証を完了した、とは主張しない。

確認した本番ファイルのSHA256：

|ファイル|SHA256|
|---|---|
|`NSP14/Endpoint/Carry.lean`|`95ba789f8bcdb85db4e7cec6072cf197f1eec1ba532163180d0c8e932d9d0702`|
|`NSP14/Endpoint/ActualKernel.lean`|`9fcb8b751d540d92bd3d0c729109ad1001af913fc44a410d6b74150ad78c9c43`|
|`NSP14/Endpoint/Stopping.lean`|`78241f0a84de913cce409c87db128a8484e2162a2d19080b4ac289d1b994c6d4`|
|`NSP14/Endpoint/CompetitorBounds.lean`|`d3d966f5a41aa8c7c91e1a6edefbfa5713cadcb0a6d37b61c48f86d7cd972bee`|
|`NSP14/Endpoint/FullTransfer.lean`|`dbe038aa0960263c5008666a5f64dd184220af04a907b019baf37139b2f784f1`|

## 6　検証と長さの扱い

全称性の根拠は3のceiling恒等式・単調性・自然数の最小値と、全j実核の既証明の同定である。
有限検算として、u=3,…,30、m=u+1,…,u+9、j∈{1,2,3,7,u}、全rと、
Hx∈{0,1,2,u−2}、L∈{0,Hx}、d∈{1,2,5}の434,700組でcarry差と高さ式を整数照合した。
r=0、s=0、gcd(m,u)>1、Hx≤2の境界を含み全件一致した。
固定sの純v冪の算術も、同じu,m範囲、Hx=0,…,u−2、j=Hx+1、全sの80,892組で照合した。
この検算を有限jによる核認定や全称証明の代替には使っていない。

章の数式区切りは一致。旧停止のtag・周期定義・carry五行表は本文から除去した。
作業前に固定したV04の49fileとV05の55file、計104fileは全SHA256が不変であることを確認した。
本番Leanへの編集やLean/lakeのfresh buildは行っていない。

本文のUnicode文字数はV05の11,788字からV06の11,848字で**60字増**、UTF-8では18,313→18,375 byteである。
必要な有限生成の根拠を明記し、極小点列と二つの順序条件を一つの表示数式へ出したため、文字数削減とは数えない。
この表示への変更は数学的内容を保った行幅調整であり、文字の縮小は行っていない。
成果は五場合のcarry表・具体周期・停止回数の証明を主比較から不要にしたことである。
独立した短いE-HEIGHTに必要な根拠を集めたので、一般Noetherian補題へ監査を外注して短く見せたものでもない。
ページ数は本担当では測定しておらず、後続の組版結果と区別する。
