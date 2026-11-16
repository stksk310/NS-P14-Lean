# V04→V05：幅章の二つの追加簡約

原稿の基礎となるLean読解SHAは `345e2d82fea50ef89e00a8f35c4fb53ac601d7ce`。
V04、本番Lean、凍結命題、既存証跡は保持する。今回の変更対象はV05の幅章と対応ノートである。
以下の二点は紙上で証明を閉じて採用した。既存Leanに同じ結論があっても、今回の新しい証明経路を実装済みとは扱わない。

## 1　非antipodal第一行：粗い尾和と整数性で全u≥8

**残す入力。** 同じ元の端点データ、q3、u≥8、実剰余集合がnon-antipodalであること、Kneserによる増分3、PC≤W、元のR+u≤W、実核を補償した第一行移行、実QC自身のfourth調和評価。

**正確な置換命題。** u≥8とし、整数nが
\[
 n\le\tfrac52W-u+5,\qquad6W\le u^2+u+6
\]
を満たせば、\(n\le\binom u2+1\)。ここでWは非負整数でも有理数でもよい。
証明は本文 (W-5I)：\(A=\binom u2+1\)、\(B=(5u^2-7u+90)/12\) とすると
\[
 A+1-B=\{(u-8)^2+17(u-8)+6\}/12>0.
\]
従って n≤B<A+1から整数性でn≤Aとなる。
Betti数への適用ではn=β1(G)とし、係数体の標数は一切制限しない。

粗い尾和は新たな仮定ではない。non-antipodalの実距離和は
\(W\le B_3=u+\sum_{j\ge0}(u-4-3j)_+\)。
等差和の一般式に \(u-4=3k+b\)、\(b\in\{0,1,2\}\) を入れると
\(6B_3=u^2+u+4+b(3-b)\le u^2+u+6\)。
三値を用いるのは剰余余項を2以下とするためだけであり、容量比較を三つの無限枝に分割しない。

**不要になる数学的仕事。** V04のB3(3j)、B3(3j+1)、B3(3j+2)という三つの厳密式、対応する三つの容量差、u8だけのfloor基点を主経路から除く。
精密距離和を付録へ移して必須にしたのではなく、粗い全域上界で十分なことを証明した。

**Lean対応。**

| 役割 | 既存export | 状態 |
|---|---|---|
| 等差和の一般剰余恒等式 | `NSP14.Width.growthVolume_remainder_identity` | 既存形式化済み |
| non-antipodal実距離和と粗い上界 | `NSP14.Endpoint.Data.five_nonAntipodal_volume`; `.five_nonAntipodal_volume_remainder` | 既存形式化済み |
| β1≤5W/2−u+5 | `NSP14.Endpoint.Data.actual_first_volume_fourth`（q3） | 既存形式化済み |
| β1≤C(u,2)+1という最終結論 | `NSP14.Endpoint.Data.actual_five_nonAntipodal_first` | 既存形式化済み。ただし既存証明はu≥12とu8–11の分岐を含む |
| 新しい整数slackの一式・上記結論の分岐なし証明 | 新規named exportなし | 紙上証明済み・新経路未形式化 |

後で形式化する場合の必要入力は上の置換命題そのものであり、既存の実sourceやtargetへのconsumerの型を変更する必要はない。

## 2　疎幅と五生成元の全高次行をW-HIGHで共有

**正確な純算術命題。** e,uは整数、e≥2,u≥e、B∈Qとし
\[
 U_i(B)=B\binom ei-u\binom{e-1}{i-1}-\binom{e-1}{i+1}.
\]
\(U_2(B)\le2\binom u3\) なら全2≤i≤eで \(U_i(B)\le i\binom u{i+1}\)。
本文W-HIGHは正規化容量を定義し、その基点・増分・隣接比を明示して証明する。
e≥6という仮定をこの純算術へ持ち込まない。

**正確な端点への接続。** 元の端点データのe=q+2とu≥eを固定し、
\[
 \beta_i(G)+\binom{e-1}{i+1}
 \le P_C\binom{e-1}i+\widehat R\binom{e-1}{i-1}
\]
が全正行で成立するとする。同じBに対しPC≤B、Rhat+u≤B、および第二行の上の数値比較があれば、
全2≤i≤eでβi(G)≤iC(u,i+1)。加法形の資源仮定はNat飽和減算と無関係である。

**二つの適用。**

- 疎幅e≥6では、従来どおりB=B(u)、u≥2e−2とし、既存のe6またはe≥7の第二行計算だけを行う。
- 五生成元u≥8では、u8にB14、u≥9にB=u²/4を使う。前者はU2=104≤112、後者は本文(W-5H)の正三次式が差を与える。両方に同じW-HIGHを適用する。

この第二の適用はantipodal/non-antipodalの区別に依存しない。原向きのPCとRhat、QC→QGの実核補償をそのまま保持する。
u8にW≤14を使う資源基点は必要なので削っていない。

**不要になる数学的仕事。** V04の五生成元第3–5行の三つの粗い二次上界、u8における三つのtarget基点、固定k4/5/6に対するC(u,k)/u²の単調性証明を主経路から除く。
第2行から全高次行への単調性は既存の純算術を共用するため、新しい一般rank定理は導入しない。
小幅u6/7の読みやすい表と条件付きR>0による第一行改善は変更しない。

**Lean対応。**

| 役割 | 既存export | 状態 |
|---|---|---|
| e≥2,u≥eで有効な容量単調性 | `NSP14.Width.normalized_capacity_monotone` と `.normalized_capacity_base`, `.normalized_capacity_step`, `.chooseRatio_adj` | 既存形式化済み。これらの型にはe≥6仮定がない |
| 元sourceの全行資源 | `NSP14.Endpoint.Data.actual_positive_rows_add` | 既存形式化済み |
| u8のB14 | `NSP14.Width.five_wordVolume_eight` | 既存形式化済み |
| 五生成元全高次行という最終結論 | `NSP14.Endpoint.Data.actual_five_higher` | 既存形式化済み。ただし既存証明は旧第3–5行の個別支払いを含む |
| 任意有理Bを受け取る端点wrapperと、そのe5適用 | 新規named exportなし | 紙上証明済み・新経路未形式化 |

新wrapperに必要な入力は、D.u≥D.q+2、(D.coreP k:Q)≤B、(D.Rhat:Q)+D.u≤B、および
\[
 B\binom{D.q+2}{2}\le2\binom{D.u}{3}+D.u(D.q+1)+\binom{D.q+1}{3}
\]
である。返す結論は全2≤i≤D.q+2について、元のfullGのtotalBetti≤iC(D.u,i+1)。
既存の加法形行資源と一般capacity exportから、正のC(e,i)での有理数比較として構成できる。

V05紙上主経路には `NSP14.Width.choose_quadratic_step` と `.choose_quadratic_from_eight` が不要となる。
これは本番Leanのimport graphを書き換えたという意味ではない。既存 `actual_five_higher` の証明とimportは保存されている。

## 今回の検証と長さの扱い

SymPy 1.14.0で六つの恒等式を記号的に0へ約分した：粗い尾和剰余式、整数slack式、u8への平行移動、容量基点、source資源のPascal整理、保持した五生成元第二行三次式。
さらに厳密整数・有理数で32,973組を検査した。範囲はe2–40,u=e,…,e+40の全2–e行、およびu8–1000の尾和・整数slack・五生成元第二行である。
新補題の低い境界e2、幅の境界u=e、top i=e、非整数B=正規化第二行容量も含み、全件成功した。
本文のTeX区切りは釣り合い、制御文字は0だった。今回Lean/lakeのfresh buildは行っていない。

有限検算は転記や境界の補助確認であり、全称性は本文の等差和恒等式・非負係数式・容量の帰納法から得る。
共通補題のstatement・適用範囲・証明を独立して明記したため、文字数だけの減少は保証しない。
今回の成果は、三剰余の容量支払いと第3–5行の別支払いを不要にしたことであり、追加のページ削減幅は組版後に別途評価する。
