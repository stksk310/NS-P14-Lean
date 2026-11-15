# V05 幅章の二候補：独立数学レビュー

**判定：以下の固定した数学差分について、修正を要する誤り・仮定の追加・範囲漏れを発見しなかった。**
V04の証明全体の再認証、ページ数、README、後で作成・変更する成果物の認証ではない。
本番Leanの新規形式化やfresh buildの成功も主張しない。

## レビューを固定する証拠

本番読解基準commitは `345e2d82fea50ef89e00a8f35c4fb53ac601d7ce`。
以下は実際に読んで照合したファイルのSHA256である。

|対象|SHA256|
|---|---|
|V04 `chapters/04_WIDTH_JA.md`|`179e66b95502fb76aeb8abda873cd742a46c7c29c702b964c0942e69d07dafaa`|
|V05 `chapters/04_WIDTH_JA.md`|`d764186ac90707fca1c40318d03eac59b077a8905c21f39a373196c8cdaafe78`|
|V05 `notes/V05_WIDTH_CHANGES_JA.md`|`a9e213d072f0943d3499549fb8b749ff9acde1900e2785e385cf5870156c82bb`|
|V05 `notes/WIDTH_AUDIT_JA.md`|`7890ce642edd221f7da56b086d4d6bee468226a35b9c164a3705a52d3d8989a4`|
|`NSP14/Width/NormalizedCapacity.lean`|`001e46887db4c6dfcbc42407dcaed3f27fffcb6705fe40045a6b2574a842de0a`|
|`NSP14/Width/FiveHigher.lean`|`fbc42e5ea06de6658e56825b0590c1050355a42ebbde94f7ae07e9e13a74de54`|
|`NSP14/Width/FiveNonAntipodal.lean`|`a4d0fce7d9dc0651f45e05d63f3b8a5c0f4e2d9adf41107ce602e394a501e5ca`|
|`NSP14/Width/SparseHigher.lean`|`4106471bb7a4c29d898c42e06057d450ae1fcc650cb7b76e188a26cf13aafb2d`|
|`NSP14/Width/SparseVolume.lean`|`08b8a080f2bbe2f6a65481a55826fd1ba55ffe4eb79034ea40614399944a9f5d`|
|`NSP14/Endpoint/PositiveRows.lean`|`ddfe975206ebe65cd579341a3a0a3127295667018b459f4be69a941efe66b9d1`|

レビューはV04→V05の新差分に集中した。変更のないordinary、N4、端点のE-STOP、APDを改めて全再導出したものではない。
これらの対応章 `02_ORDINARY_JA.md`, `03_ENDPOINT_JA.md`, `04A_ANTIPODAL_JA.md`, `05_N4_JA.md` がV04とV05でbyte一致することを別に確認した。
幅章自身の端の二幅・dense・u6/7の表・最後のcoverageもbyte一致する。

## 1　W-HIGHの範囲と全行移行

命題は整数e≥2,u≥e、任意有理数B、全2≤i≤eに対する純算術である。
分母C(e,i)はこの範囲で正であり、Bの正値性を追加する必要はない。
`Ui(B)<=i*C(u,i+1)` と `B<=Ti(u)` の同値に順序反転や自然数減算は入らない。

基点は二項係数比を使って、整数減算ではなく有理数の式として

\[
 \begin{aligned}
 \mathcal T_i(e)
 &=\frac{i(e-i)}{i+1}+i+
       \frac{(e-i)(e-i-1)}{e(i+1)}\\
 &=e-1+\frac ie
 \end{aligned}
\]

と再導出できる。i=eでも最後の分子は0で、e−iによる除法はない。
幅1の増分はPascal式から `i*C(u,i)/C(e,i)+i/e`。
`Ri=C(u,i)/C(e,i)>0` の隣接比は、i<eに限り `(u-i)/(e-i)>=1`。
よってRiとiがともに非減少であるためiRi+i/eも非減少となる。
基点と各増分の比較を幅uに沿って足せば、全2≤i≤eでTi(u)≥T2(u)が従う。
e=2では比較対象がi=2だけとなり、同じstatementに入る。

特にtopでは `Ue(B)=B-u`、`Te(u)=e*C(u,e+1)+u` であり、
topだけ別の未証明比較を必要としない。既存の
`normalized_capacity_base`, `normalized_capacity_step`, `chooseRatio_adj`,
`normalized_capacity_monotone` の型にもe≥6仮定はなく、紙上の範囲明示は正当である。

端点への適用は、**同じ元のcoreとactual G**の加法形(W-G)、PC≤B、Rhat+u≤Bから

\[
 \beta_i(G)\le
 B\binom{e-1}i+(B-u)\binom{e-1}{i-1}-\binom{e-1}{i+1}
 =U_i(B)
\]

を有理数として導く。ここでは二つの二項係数が非負なので、各資源上界の代入方向は正しい。
PをPGに置き換えたり、反射したcoreのRhatを使ったりしていない。
任意有理Bを受け取るこの数値wrapper・端点consumerを、今回新しいnamed Lean exportとして追加したとは扱わない。
一般capacityの構成要素が既存形式化済みであることと、新しい証明経路の形式化は区別されている。

## 2　五生成元高次行への適用

この適用ではe=5,u≥8なのでW-HIGHのu≥eを満たす。
全構造に有効な `4W<=u^2` とPC≤W、Rhat+u≤Wを使うため、
antipodalとnon-antipodalの区別は不要である。

- u=8では保持した等差尾和がW≤14を与える。B=14ならPC≤14、Rhat≤6で、
  `U2(14)=10*14-4*8-4=104<=112=2*C(8,3)`。
- u≥9ではB=u²/4が両資源を同時に抑え、第二行の差はz=u−9として
  `(2*z^3+33*z^2+136*z+33)/6>0`。

両方とも同じW-HIGHが全2–5行、topを含めて返す。
u=8の資源基点を不要化したという主張ではなく、第3–5行の別の粗上界・別基点・
`C(u,k)/u^2`の単調性を不要化したものである。
既存 `actual_five_higher` は別経路による同じ結論であり、そのproofを今回書き換えたわけではない。

## 3　non-antipodal第一行の粗尾和と整数閾値

新しい尾和式は、u−4=3k+b、b=0,1,2に対する有限等差和の恒等式から

\[
 6B_3=6u+(u-4)^2+3(u-4)+b(3-b)
       =u^2+u+4+b(3-b)\le u^2+u+6
\]

と再導出できる。等差和のこの恒等式は任意正整数の公差sで成立し、
sをKneserの一般粗増分ceil(a/2)に固定する追加制約はない。
従ってnon-antipodalで得た増分3にa=4,s=3として使える。
bを三値で抑えることは余項の上界であり、三つの容量比較の無限枝を残してはいない。
実距離和W≤B3を合わせれば `6W<=u^2+u+6`。
この粗い実資源上界は本番の `five_nonAntipodal_volume_remainder` にも既に存在する。

第一行の既存評価は実QCのfourth評価と実核補償により
`beta1<=5W/2-u+5`。したがって

\[
 \beta_1\le B=(5u^2-7u+90)/12,
 \qquad A=\binom u2+1\in\mathbb Z,
\]
\[
 A+1-B=(u^2+u-66)/12
       =\{(u-8)^2+17(u-8)+6\}/12>0.
\]

よってbeta1<Bのような不必要なstrict仮定を置かず、beta1≤B<A+1と整数性だけでbeta1≤Aを得る。
最も小さいu=8ではB=59/2、A=29、slackは1/2であり、strict性が失われない。
この整数性はtotal Betti数の整数性であり、基礎体の中での除法・標数の制限ではない。
旧三剰余の厳密式・三つの差・u8特例は新証明の前提になっていない。

## 4　元のsourceと物理targetへの帰還

新二経路はいずれも、元の向きのPC、W、Rhatを共有する(W-G)/(W-T)の後に適用される。
元sourceを別半群に変更する新操作はない。
高次行の結論 `beta_i<=i*C(u,i+1)` はFmin_i(u)以下、第一行はFmin_1(u)そのものである。
新適用ではu≥8かつi≤5、疎幅でもu≥eなので、共通容量補題のi≤uという範囲も満たす。
V=du≥uと共通容量単調性により、literal interval completionへ支払える。
第0行とi>eは従来の共通接続のままで、完全APのd=1等の別枝を新一般容量で置き換えていない。

## 独立照合と認定の限界

可読性については、独立したW-HIGHのstatement追加は適度と判断する。
必要な自由パラメータはe,u,Bだけであり、同じ補題を疎幅と五生成元が直後に実際に共用する。
定義・基点・増分・topの分母条件が一箇所にまとまり、未使用の閉じた展開式も増やしていない。
non-antipodal側の整数閾値はu8のslack1/2まで同じ式で追え、三剰余の差表より監査しやすい。
独立statementと適用条件を明示したため本文の文字数が増えることはあるが、
その増加自体を数学的な短縮の失敗やページ削減と解釈すべきではない。
本レビューでは組版を測定しておらず、ページ減の成否を認定していない。

レビュー側で実行した記号照合では、基点の有理式、粗尾和余項、第一行B、整数slack、
u8への平行移動、五生成元第二行三次式の6恒等式を厳密に0へ約分した。
別に正確な整数・有理数でe=2–20,u=e,…,e+20の全2–e行の3,990組について、
基点・増分・T2以下でないことを照合し、u8の104≤112と整数slack1/2も確認した。
有限照合は転記と境界の補助であり、全称性の根拠は上の基点・増分・隣接比・正係数式である。

この判定が対象とするのは、記録したSHAの幅章の二つの新数学経路と、その形式化境界の説明である。
後で変更するREADME、ページ数・組版、一般の公刊原典全体、V04から変更のない証明全体、
今後のLean実装・fresh build・公開操作は認定範囲に含めない。
