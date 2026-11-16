# N4 primitive 第一行の独立監査・再証明

2026-11-09。担当範囲は、真正四生成元

\[
\Gamma=\langle m,m+a,m+b,m+w\rangle,\qquad
0<a<b<w<m,\quad\gcd(a,b,w)=1
\tag{P1}
\]

の接錐の**第一 Betti 数**である。今回の N4 が必要とするのは
\(w\le m-2\) であり、以下の一般上界は少し広い \(m>w\) で証明する。
\((a,b,w)=(1,w-1,w),4\le w\le10\) の直接支払いは別担当の
R24-N02 監査との合成箇所として明示する。高次行を本稿だけで認定しない。

結論：R27-A01 の二面支持、pure power cap、有限 core リストの完全性、
五支持の実最小禁止数、全 \(m\) 上界、および \(w\ge48\) の比較に穴を認めなかった。
有限残余は著者の合同候補リストと別のアルゴリズムで全 13,921 件を再構成した。
例外は正確に \((1,w-1,w),3\le w\le10\) である。
以下は既存の PASS 表示を証明として使わず、定義から計数までを記す。

## 1. 原典同一性・外部入力・残る合成箇所

主原典は
`source_material/NS_WIDTH_P14_CANONICAL_PROOF_HANDOFF_R01_R57_20261109/04_HISTORICAL_THEOREMS/R27_LITERAL_PROOFS.md`
の ORIGINAL
`R27/research/a/R27_A01_PRIMITIVE_FOUR_ALL_ROWS_SUPPORT_CAPACITY_JA.md`。
OBJECT_INDEX の byte range offset=217209, size=19077 を実際に読み、SHA-256

`defb8fb07b36c3de12b2df5fe4c0645cffc58759a6eb0934c98fa6c124c6f276`

と一致することを確認した。記録は `source_identity.json`。

使用する外部の数学的定理は Savchev–Chen の次だけである。

> 巡回群 \(\mathbb Z/n\mathbb Z\) の零和のない列の長さが \(n/2\) を超えるなら、
> ある unit を全項に掛けた後の least positive representative の総和は \(n\) 未満。

S. Savchev and F. Chen, *Long zero-free sequences in finite cyclic groups*,
Discrete Mathematics 307 (2007), 2671–2679,
DOI `10.1016/j.disc.2007.01.012`;
[著者 preprint, §4 Theorem 8](https://arxiv.org/html/math/0602568v1)。
この担当の shell からの arXiv 取得は環境 proxy の 403 で失敗した。
root が別の閲覧手段で一次本文の §4 Theorem 8 と unit 条件を直接確認し、
上記 statement と完全一致することを共有した。本稿はその共有された一次照合に加え、
定理の各仮定と以下の適用を独立に確認している。
Savchev–Chen 定理の原証明そのものを本稿で再証明した、とは主張しない。

依存状態は次のとおり。

|入力・旧祖先|本稿での実確認状態|
|---|---|
|R27-A01 §§2–7|原文を全文読み、以下で独立再導出。原文ハッシュも照合|
|Savchev–Chen Theorem 8|外部公刊定理として使用。一次 statement は root が直接照合、適用は本担当が検証|
|R26-A01 の内部長 \(s+t\le w-2\)|§5 の混合補題と pure cap だけから導出し直すため、第一行の依存から除去|
|R24-N01 の core/endpoint 同定|必要な \(D\) の意味を §4 で直接証明。第一行の一般上界は旧 endpoint 模型を呼ばない|
|R26-R01 の disjoint-support 補題|§6 で一行の最小性論証から直接証明。旧 ratio theorem は呼ばない|
|interval 第一行の公式|§2 で rational normal curve の交換と bad fiber から独立証明|
|有限 offset 証書|§9 の direct-fiber DP で全件を新規完全計算。著者コードを import せず、原合同候補リストも使わない|
|R24-N02 boundary \((1,w-1,w),4\le w\le10\)|本担当は認定しない。別担当の全 \(m\ge w+2\) 証明との合成箇所|
|R26-A01 高次行、R25 rank/TU、K02|第一行の本証明には不要。高次行監査は別担当|

## 2. actual interval target の第一容量を直接導く

\(m>w\) なので、source の四元も target の \(m,m+1,\ldots,m+w\) も
\([m,2m)\) にあり、全て真正な最小生成元である。
\(\gcd(a,b,w)=1\) から source の生成系 gcd も 1。
target は同じ multiplicity \(m\) と物理幅 \(w\) の actual completion である。

target の斉次 core を

\[
C_w=k[s,st,\ldots,st^w]
\]

とし、fiber \((d,n)\) は通常次数 \(d\)、offset \(n\) を意味する。
この fiber は \(0\le n\le dw\) のとき一次元、そうでなければ零である。
なぜなら \(0,1,\ldots,w\) の \(d\) 個の和は区間 \([0,dw]\) を全て埋めるからである。

core ideal は二次交換で生成される。同じ和を保つ交換
\(X_iX_j\leftrightarrow X_{i'}X_{j'}\) により、一つの内部因子を除いて
端点因子 \(X_0,X_w\) だけの word に直せる：
内部の二因子の和が \(w\) 以下なら \(X_0X_{i+j}\)、
\(w\) 以上なら \(X_{i+j-w}X_w\) に置く。
したがって同じ次数・offset の全単項式は二次交換で連結する。
core の最小二次関係の個数は

\[
\dim k[X_0,\ldots,X_w]_2-\dim(C_w)_2
=\binom{w+2}{2}-(2w+1)=\binom w2.
\tag{T1}
\]

fiber \((d,n)\) の実 weight は \(dm+n\)。この word が接錐で零になることは、
長さ \(d+\ell\), \(\ell\ge1\) の表示があることと同値であり、
その offset は \(n-\ell m\) である。したがって零なら \(n\ge m\)。
逆に \(n\ge m\) なら \(0\le n-m\le dw-m<(d+1)w\) なので、
offset \(n-m\) を長さ \(d+1\) で表示できる。従って bad fiber は正確に \(n\ge m\)。

\(d_0=\lceil m/w\rceil\ge2\) と置く。この bad ideal の最小生成 fiber は正確に

\[
d=d_0,\qquad m\le n\le d_0w.
\tag{T2}
\]

実際、次数 \(d_0-1\) では最大 offset が \((d_0-1)w<m\) なので、
(T2) は既存の bad fiber と一次因子の積にならない。
\(d>d_0\) と \(m\le n\le dw\) に対しては

\[
\max(0,n-(d-1)w)\le i\le\min(w,n-m)
\]

を満たす整数 \(i\) が存在する：\((d-1)w\ge m\) と \(n\le dw\) がそれを保証する。
従って \((d,n)=(d-1,n-i)+(1,i)\) で、前の fiber は bad。
これを繰り返すと (T2) で生成される。

core の二次関係と (T2) の \(d_0w-m+1\) 本の monomial lift は接錐 ideal を生成する。
core の最小関係は全て次数 2 で、接錐 ideal には一次式がないので、その最小性は失われない。
追加 lift の最小性と独立性は \(\mathrm{bad}/(C_w)_+\mathrm{bad}\) の異なる fiber 基底から従う。
よって任意体上で

\[
F_1=\beta_1(G_{\widetilde\Gamma})
=\binom w2+d_0w-m+1
=\binom w2+w-((m-1)\bmod w)
\ge F_{\min}:=\binom w2+1.
\tag{T3}
\]

これにより、本稿では interval の外部 Betti 公式を前提にしない。

## 3. source core の二面支持と pure powers

\[
S=k[x,y,z,v],\qquad C=k[s,st^a,st^b,st^w],\qquad I_C=\ker(S\to C).
\]

通常次数 \(d\)、offset \(n\) を二重次数とする。
単項式を \((a\deg_y+b\deg_z,\ d,\ \mathrm{lex}_{y>z>x>v})\) で比較する。
これは乗法と両立する全順序で、第一重みが零の因子にも第二の正の通常次数があるので
well-order であり、1 が最小となる global monomial order である。
\(J_0=\operatorname{in}(I_C)\) とする。

core の各非零二重次数 fiber は一次元であるから、\(J_0\) の最小生成元 \(g\) に対し、
同じ次数・offset の標準単項式 \(h\) を取り \(g-h\in I_C\) とできる。
\(g,h\) に共通変数があれば、共通因子で割った binomial の先頭項が \(g\) を真に割るので
\(g\) の最小性に反する。従って \(g,h\) は互いに素である。

* \(v\mid g\) とすると \(v\nmid h\)。同じ offset を \(n\) としたとき、
  \(g\) の内部重みは \(n-w\deg_v(g)<n\)、\(h\) の内部重みは \(n\)。
  よって \(g\) は先頭項になれない。
* \(xyz\mid g\) とすると、相手 \(h\) は純 \(v\) 冪。
  同じ次数における平均 offset は \(g\) では \(w\) 未満、\(h\) では \(w\) なので不可能。
* \(xy\mid g\) かつ \(z\nmid g\) とすると、\(h\) は \(z,v\) のみを使う。
  平均 offset が左では高々 \(a\)、右では少なくとも \(b>a\) となり不可能。

従って

\[
\operatorname{Min}(J_0)\subset k[y,z]\ \cup\ k[x,z].
\tag{C1}
\]

特に \(J_0\) は \(v\) を含まず、正 \(x\) を持つ最小生成元には \(y\) がない。

\[
p=\min\left(\frac b{\gcd(a,b)},\frac w{\gcd(a,w)}\right),\qquad
q=\min\left(\frac{w-a}{\gcd(w-a,w-b)},\frac w{\gcd(b,w)}\right).
\tag{C2}
\]

\(g=\gcd(a,b)\) とした関係
\(y^{b/g}=x^{(b-a)/g}z^{a/g}\) は内部重みが等しく lex により左が先頭。
\(y^{w/\gcd(a,w)}\) と \(z^{w/\gcd(b,w)}\) の endpoint 零和関係では
内部重みの大きい純内部側が先頭。
また \(h=\gcd(w-a,w-b)\) とすると

\[
z^{(w-a)/h}=y^{(w-b)/h}v^{(b-a)/h}
\]

も左が内部重みの大きい先頭項である。従って \(y^p,z^q\in J_0\)。
最小純冪指数を \(p_0,q_0\) と書くと

\[
2\le p_0\le p\le b\le w-1,\qquad
2\le q_0\le q\le w-a\le w-1,
\tag{C3}
\]

\[
p_0\le\frac w{\gcd(a,w)},\qquad q_0\le\frac w{\gcd(b,w)}.
\tag{C4}
\]

下端が 2 であるのは、四つの一次 generator が異なる offset を持つため、一次関係がないからである。

### 3.1 原有限候補リストの完全性も確認する

指数を \((X,s,t)\) とし、\(x^Xy^sz^t\) を表す。次の候補全体から可除なものと重複を除くと
正確に \(\operatorname{Min}(J_0)\) となる。

1. \((0,p,0),(0,0,q)\)。
2. \(0\le s\le p,0\le t\le q,s+t>0\) で \(as+bt\equiv0\pmod w\) の \((0,s,t)\)。
3. \(1\le s\le p,0\le t\le q,as-bt=Kw\ge0,s\ge t+K\) の \((0,s,0)\)。
4. \(1\le t\le q,0\le s\le p,bt-as=Kw>0\) の
   \((\max(0,s+K-t),0,t)\)。

候補の包含はそれぞれ上の pure 関係、
\(y^sz^t=x^{s+t-K}v^K\)、
\(y^s=x^{s-t-K}z^tv^K\)、
\(x^{s+K-t}z^t=y^sv^K\) または \(z^t=x^{t-s-K}y^sv^K\)
から従う。最後は \(K>0\) により先頭側が決まり、全指数は記載された枝で非負である。

逆に (C1) で支持を尽くす。混合 \(y^sz^t\) の標準相手は互いに素なので \(x,v\) だけを使い、
候補 2 に属する。純 \(y^s\) の相手は \(x^Az^tv^K\) で、標準性より \(t<q_0\le q\)；
次数・offset 等式が候補 3 を与える。純 \(z^t\) の相手は \(x^Ay^sv^K\) で
\(s<p_0\le p\)；\(K=0\) なら相手の正 \(y\) によって逆に相手が先頭となるので \(K>0\)、候補 4。
正 \(x\) の場合は \(x^Xz^t-y^sv^K\) しかなく、\(t<q_0,s<p_0\)、同じく \(K>0\) で候補 4。
純冪 cap により先頭側の \(s,t\) も範囲内である。
よって有限候補リストの逆包含に探索上の仮定はない。

## 4. 内部標準 word と endpoint 表示

\[
D=\{(s,t)\in\mathbb N^2:y^sz^t\notin J_0\},\quad
B=|D|,\quad K_0=\mu(J_0),
\]

\[
\phi(s,t)=(w-a)s+(w-b)t,\qquad M=\max_{D}\phi(s,t).
\tag{C5}
\]

\(D\) は、「同じ次数・offset に端点 \(x\) または \(v\) を含む表示がない」内部 word の集合と正確に一致する。
これを旧 endpoint 模型に頼らず証明する。

内部 word \(g=y^sz^t\) に endpoint 表示 \(h=x^Ay^uz^rv^K\) があるとする。
\(K>0\) なら \(h\) の内部重みが小さいので \(g\in J_0\)。
\(K=0,A>0\) なら、次数と offset の等式から

\[
(s-u)+(t-r)=A>0,\qquad a(s-u)+b(t-r)=0,
\]

従って \(s-u=bA/(b-a)>0\)。lex によりやはり \(g\) が先頭。
逆に内部 word が非標準なら、同じ次数・offset の異なる純内部 word は存在しない
（二本の一次方程式と \(a\ne b\) により一意）ので、その標準形は endpoint を含む。
これで同値が示された。また \(D\) は \(C/(x,v)C\) の単項式基底でもある。

## 5. 混合 word 長と無界幅に用いる三つの評価

\((s,t)\in D\), \(s,t>0\) とする。\(s\) 個の \(a\)、\(t\) 個の \(b\) を
\(\mathbb Z/w\mathbb Z\) の列とみなす。
非空零和部分列の長さを \(d\)、通常の整数和を \(Kw\) とすると、各 offset が \(0,w\) の間なので
\(1\le K\le d-1\)。対応因子を \(x^{d-K}v^K\) に直せて endpoint 表示を与える。
§4 に反するので、この列は零和のない列である。

\(s+t>w/2\) と仮定し Savchev–Chen を適用する。
unit 倍後の二種類の positive representative が両方 2 以上なら総和は
\(2(s+t)>w\) となる。従って一方は 1、他方は \(c\ge2\)。
元の offset を順に \(\alpha,\beta\)、その個数を \(R,T\ge1\) とする。
unit 性から \(c\alpha-\beta\) は \(w\) の倍数なので

\[
c\alpha=\beta+kw.
\]

ここで \(c\alpha-\beta>-w\) と \(c\alpha-\beta<cw\) より
\(0\le k\le c-1\)。従って core の関係

\[
Y_\alpha^c=x^{c-1-k}Y_\beta v^k
\tag{C6}
\]

は非負指数を持ち、右に endpoint 因子が合計 \(c-1>0\) 個ある。
\(D\) の意味から \(R<c\)。Savchev–Chen の総和は整数であるから \(R+cT\le w-1\)。
よって

\[
2(R+T)=(R+cT)+(R-(c-2)T)
\le(w-1)+(c-1-(c-2))=w,
\]

仮定と矛盾する。従って

\[
\boxed{(s,t)\in D,\ st>0\Longrightarrow s+t\le h:=\lfloor w/2\rfloor.}
\tag{C7}
\]

pure word は (C3) より長さ高々 \(w-2\)。混合 word は (C7) より
\(\lfloor w/2\rfloor\le w-2\)（\(w\ge3\)）。したがって **旧 R26 の内部長補題を使わず**

\[
s+t\le w-2\quad((s,t)\in D),\qquad M\le(w-2)(w-1).
\tag{C8}
\]

混合 word は \(s,t\ge1,s+t\le h\) の格子点なので高々 \(\binom h2\) 個。
軸上は単位元を一度だけ数えて \(p_0+q_0-1\) 個。よって

\[
B\le\binom h2+p_0+q_0-1
\le\frac{w^2}{8}+\frac{7w}{4}-3.
\tag{C9}
\]

また \(yz\) 面の最小生成元は \(z\) 指数が \(0,\ldots,q_0\) の各値に高々一つ、
正 \(x\) の最小生成元は \(z\) 指数が \(1,\ldots,q_0-1\) の各値に高々一つ。
各々同じ \(z\) 指数なら他方が可除になるからである。従って

\[
K_0\le(q_0+1)+(q_0-1)=2q_0\le2w-2.
\tag{C10}
\]

## 6. actual 接錐の初期 ideal と共通因子禁止

\(\nu(n)\) を \(n\in\Gamma\) の実最大表示長とする。
core fiber \((d,n)\) の実 weight は \(dm+n\) であり、その接錐への像が非零であることは
\(\nu(dm+n)=d\) と同値。\(\nu(dm+n)>d\) の core 単項式を bad と呼ぶ。
同じ次数の異なる offset は異なる実 weight を持つので、非零像は線形独立。
したがって \(C\to G\) の kernel は正確に bad fiber からなる monomial ideal である。

\(I_G=\ker(S\to G)\), \(J_*=\operatorname{in}(I_G)\) とすると、
\(J_*\) は \(J_0\) と bad な core 標準単項式を合わせた monomial ideal である。
これは同じ次数・offset の全単項式が core で同じ fiber に落ち、その fiber 全体が
接錐で非零か零かの二択であることから直ちに従う。

非core の最小生成元 \(g\in\operatorname{Min}(J_*)\setminus J_0\) は core 標準で bad。
\(g\) と同じ実 weight を持ち次数が \(\ell\ge1\) だけ大きい単項式 \(h\) を取る。
**任意のこのような長い表示 \(h\) は \(g\) と互いに素である。**
共通変数で割ると \(g\) の真の divisor が同じ正の次数差を持つ長い表示を得て bad となり、
\(g\) の \(J_*\)-最小性に反するためである。

正 \(x\) の \(g\) が \(y,z\) を共に含む場合、\(v\nmid g\) なら長い相手は純 \(v\) 冪、
\(v\mid g\) なら相手に使える変数がない。後者は明らかに不可能。
前者も、\(g\) の全数値因子は \(m+w\) 未満なのに、長い純 \(v\) 冪はそれより多い個数の
最大数値生成元を持つので同じ実 weight になれない。
従って正 \(x\) を含む bad 最小生成元では \(y,z\) の少なくとも一方がない。

## 7. 五支持の全数と全 multiplicity を消した \(U\)

次を定義する。

\[
A_0=\max\left(0,\left\lfloor\frac{M-2w-1}{w}\right\rfloor\right),
\tag{U1}
\]

\[
L_y=\sum_{r=1}^{p_0-1}\max\left(0,
\left\lfloor\frac{r(w-a)-2w+b}{2w+1}\right\rfloor\right),
\]

\[
L_z=\sum_{r=1}^{q_0-1}\max\left(0,
\left\lfloor\frac{r(w-b)-2w+a}{2w+1}\right\rfloor\right).
\tag{U2}
\]

いずれも \(a,b,w\) だけの量である。

### I. \(x\) を含まない支持：高々 \(B\)

\(g=y^sz^tv^K\) と書く。\(J_0\) が \(v\) を含まないので \((s,t)\in D\)。
固定した \((s,t)\) で異なる \(K\) があれば一方が他方を割るため、最小生成元は高々一つ。
\((s,t)=(0,0)\) の純 \(v\) 冪も、この費用 \(B\) に含む。

### II. 正 \(x\), \(v=0\)：高々 \(q_0-1\)

純 \(x\) 冪は同 weight の長い表示を持てない（各数値生成元が少なくとも \(m\)）。
\(xy\) 支持では相手は \(z,v\) のみを使い、相手の全数値生成元は source 因子より大きく、
個数も多いので不可能。§6 の排除と合わせ、残るのは
\(g=x^Az^t,A,t\ge1,t<q_0\)。固定 \(t\) に最小 \(A\) は高々一つ。

### III. \(xv\) 支持：高々 \(A_0\)

\(g=x^Av^K,A,K\ge1\)。長い相手は共通因子禁止により純内部 word。
core 標準化が endpoint を導入すれば共通因子を持つ別の長い表示となるので、
相手は \(y^sz^t,(s,t)\in D\) と取れて、実際その範囲を外れられない。
次数差が \(\ell\) なら、次数・実 weight 等式より

\[
wA=\phi(s,t)-\ell(m+w)\le M-2w-1,
\tag{U3}
\]

最後は \(m>w\) と \(\ell\ge1\)。固定した正 \(A\) では最小の \(K\) は高々一つだから費用は (U1)。
(C8) より、\(w\ge5\) では

\[
A_0\le\max\left(0,\left\lfloor\frac{w^2-5w+1}{w}\right\rfloor\right)=w-5.
\tag{U4}
\]

### IV. \(xyv\) 支持：高々 \(L_z\)

\(g=x^Ay^sv^K,A,s,K\ge1\)。長い相手は \(z^r\) のみ。
\(r\ge q_0\) なら \(z^{q_0}\) の core 関係を代入し、同じ次数・offset の別表示が
\(x,y,v\) の少なくとも一つを含む。この表示はなお長く、\(g\) と共通因子を持つため矛盾。
従って \(1\le r<q_0\)。また \(g\) 自身が core 標準なので \(1\le s<p_0\)。

\[
r=A+s+K+\ell,\qquad \ell m=as+wK-rb,
\]

\[
as\equiv rb+\ell m\pmod w.
\tag{U5}
\]

固定 \((r,\ell)\) に対し、(U5) の整数解が存在するなら、その \(s\) の間隔は
\(w/\gcd(a,w)\)。区間 \(1\le s<p_0\le w/\gcd(a,w)\) には高々一解しかない。
\(s\) が決まれば実 weight 式で \(K\)、次数式で \(A\) も一意となる。
したがって各 \(g\) に長い表示を一つ選ぶと \(g\mapsto(r,\ell)\) は単射である。
原 offset が 1 であることも、合同式に全剰余で一意解があることも仮定していない。

さらに

\[
\ell(m+w)=r(w-b)-wA-s(w-a)
\le r(w-b)-2w+a.
\]

\(m+w\ge2w+1\) なので、固定 \(r\) で取り得る正 \(\ell\) の個数は
(U2) の \(L_z\) の対応する summand 以下である。

### V. \(xzv\) 支持：高々 \(L_y\)

\(g=x^Az^tv^K,A,t,K\ge1\)。相手は純 \(y^r\) で、同じ core 代入論証により
\(1\le r<p_0\)。\(g\) の標準性より \(1\le t<q_0\)。合同式は

\[
bt\equiv ra+\ell m\pmod w.
\]

解の間隔 \(w/\gcd(b,w)\) と (C4) から \((r,\ell)\) への単射。
また

\[
\ell(m+w)=r(w-a)-wA-t(w-b)\le r(w-a)-2w+b,
\]

なので費用は \(L_y\) 以下となる。

以上の五つは互いに重ならず、§6 と純 \(x\)、\(xy\) の排除により非core 最小生成元を尽くす。
どちらの三変数支持も捨てていないし、反射 source に移して費用を流用してもいない。
従って同じ actual source に対し

\[
\mu(J_*)\le U(a,b,w):=K_0+B+(q_0-1)+A_0+L_y+L_z.
\tag{U6}
\]

最後に \(\beta_1^S(G)=\mu(I_G)\le\mu(J_*)\)。
この不等式に高次 Betti の退化定理は要らない。
各最小単項式生成元を先頭項に持つ \(I_G\) の式を一つずつ取れば、それらは Gröbner basis で、
通常の除法により \(I_G\) を生成するからである。どの体でも同じ議論が通る。
よって

\[
\boxed{\beta_1(G)\le U(a,b,w)\quad\text{for every }m>w.}
\tag{U7}
\]

ここで初めて \(m\) が完全に除去される。後の有限 offset 計算の論理的前提は (U7) である。

## 8. \(w\ge48\) の無限定理

(U2) の各零切り上げ・床・負の項を落とし、非負の上界で評価すると

\[
L_y+L_z\le\frac{(w-a)p_0^2+(w-b)q_0^2}{4w}
\le\frac{(w-a)b^2+(w-b)(w-a)^2}{4w}\le\frac{w^2}{4}.
\tag{W1}
\]

最初の評価は \(\sum_{r=1}^{p_0-1}r=p_0(p_0-1)/2\) と \(2w+1>2w\) による。
最後を確認するには \(A=w-a\le w,B=b\le w\) として

\[
AB^2+(w-B)A^2\le w[B^2+w(w-B)]\le w^3,
\]

最後は \(B^2\le wB\) である。
(C9),(C10),(U4), \(q_0-1\le w-2\), (W1) を足すと、\(w\ge5\) に対して

\[
U\le\frac{3w^2}{8}+\frac{23w}{4}-12.
\tag{W2}
\]

actual target の最小容量 (T3) との差は

\[
F_{\min}-\left(\frac{3w^2}{8}+\frac{23w}{4}-12\right)
=\frac{w^2-50w+104}{8}.
\]

\(w=48+z,z\ge0\) と書くと分子は \(z^2+46z+8>0\)。したがって全 \(w\ge48\)、
全 \(a,b,m\) に第一行比較が成立する。有限幅や有限 multiplicity からの外挿ではない。

## 9. 残る有限領域を別アルゴリズムで完全評価する

残る入力は正確に

\[
3\le w\le47,\quad1\le a<b\le w-1,\quad\gcd(a,b,w)=1.
\tag{F1}
\]

`independent_offset_audit.py` は標準ライブラリだけを使い、著者コードや旧出力を入力にしない。
特に §3.1 の合同候補リストを実装していない。
offset の一変数最短 word 問題から初期 ideal を直接復元する。

### 9.1 direct-fiber アルゴリズムの完全性

\(L(n)\) を、offset \(n\) を \(a,b,w\) で表示する最短個数とする（不可能なら \(\infty\)）。
\(L(0)=0\) と漸化式

\[
L(n)=1+\min\{L(n-a),L(n-b),L(n-w)\}
\tag{F2}
\]

（負の添字を除く）で厳密に求める。これは \(n\) に関する帰納法で完全。
正 \(v\) を一個以上持つ表示の最短長は

\[
E(n)=\begin{cases}1+L(n-w)&n\ge w,\\\infty&n<w.\end{cases}
\tag{F3}
\]

純内部 \(y^sz^t\), \(d=s+t,n=as+bt\) に対し

\[
y^sz^t\in J_0\quad\Longleftrightarrow\quad L(n)<d\ \text{or}\ E(n)\le d.
\tag{F4}
\]

左向き：前者は余った次数を \(x\) で埋める endpoint 表示、後者は \(v\) を持つ表示。
右向き：§4 による endpoint 表示は、\(x>0\) で \(v=0\) なら offset 表示長が \(d\) 未満、
\(v>0\) なら \(E(n)\le d\)。

一方、\(x^Xz^t\) は \(n=bt,d=X+t\) を持つ。
\(v\) を使わない別表示がある場合、それは正 \(y\) を含み、lex で元の word より大きい。
したがって元より小さい表示があることは正 \(v\) 表示があることと同値であり

\[
x^Xz^t\in J_0\quad\Longleftrightarrow\quad X+t\ge E(bt).
\tag{F5}
\]

\(E(bt)<\infty\) のとき閾値は \(X=\max(0,E(bt)-t)\)。
これが direct-fiber core 構成である。

有限化は (C1)–(C3) により正当化される。
\(yz\) 面の最小生成元は \(0\le s\le p,0\le t\le q\) 内にあり、(F4) で全件判定できる。
正 \(x\) の最小生成元は \(1\le t<q_0\le q\) にあり、各 \(t\) で (F5) の閾値を一つ追加すれば十分。
可除な候補を除いて得られるものは、従って正確に \(\operatorname{Min}(J_0)\)。
DP が必要とする \(n\) は高々 \(ap+bq\) であり、これを超える不明な fiber は参照しない。
\(D\) 自体も \(0\le s<p,0\le t<q\) に対する (F4) で直接計算する。

これにより各 offset において \(K_0,p_0,q_0,D,B,M,A_0,L_y,L_z,U\) を厳密整数で得る。
core の最小生成元から得た membership と (F4) の全箱内 membership が一致することも毎回検査する。
符号付き rank や数値近似は使わない。

### 9.2 全領域・出力

幅ごとの入力個数はループ結果に加えて、独立に Möbius 反転

\[
N(w)=\sum_{d\mid w}\mu(d)\binom{w/d-1}{2}
\tag{F6}
\]

でも照合した。\(a,b,w\) が共通 divisor \(d\) を持つ組の個数が
\(\binom{w/d-1}{2}\) であることから (F6) が従う。
\(\sum_{w=3}^{47}N(w)=13921\)。

新規証書は `independent_offset_certificate.json.gz`、概要は
`independent_offset_summary.json`。証書内 payload の canonical JSON の SHA-256 は

`43d50ab43a88bee6648312b10e7a8c539edce06ccf938768ba64fa26bcdaf0ef`。

全組で (C3),(C7)–(C10),(W1) の整数版、正確な core membership を計算し、
\(U>F_{\min}\) は正確に

\[
\boxed{(a,b,w)=(1,w-1,w),\quad3\le w\le10.}
\tag{F7}
\]

となった。幅別最小 slack \(F_{\min}-U\) は以下。

|\(w\)|個数|最小 slack|\(w\)|個数|最小 slack|\(w\)|個数|最小 slack|
|---:|---:|---:|---:|---:|---:|---:|---:|---:|
|3|1|-3|18|99|27|33|450|168|
|4|3|-4|19|153|33|34|408|182|
|5|6|-4|20|132|40|35|540|196|
|6|9|-5|21|174|46|36|414|210|
|7|15|-5|22|165|54|37|630|225|
|8|18|-4|23|231|62|38|513|241|
|9|27|-4|24|180|70|39|636|256|
|10|30|-2|25|270|79|40|552|273|
|11|45|0|26|234|89|41|780|290|
|12|42|2|27|297|98|42|558|307|
|13|66|5|28|270|109|43|861|325|
|14|63|9|29|378|120|44|690|344|
|15|84|12|30|276|131|45|828|362|
|16|84|17|31|435|143|46|759|382|
|17|120|22|32|360|156|47|1035|402|

新計算の完了後、原著者出力の全 13,921 行とも比較し、core 最小生成元、pure caps、
\(B,M,A_0,L_y,L_z,U\)、容量、slack が全件一致した。
この後比較は独立計算の入力ではなく、二実装の相互検査である。

再実行：

```bash
python n4_work/primitive_first/independent_offset_audit.py > n4_work/primitive_first/independent_offset_summary.json
```

全 \(m>w\) の理論上界 (U7) を評価した有限残余なので、有限 \(m\) grid の全称への外挿はない。

## 10. 例外との接続・監査の結論

(F7) の \(w=3\) は \((a,b,w)=(1,2,3)\) で、source が actual interval target そのもの。
\(4\le w\le10\) は \(\Gamma=\langle m,m+1,m+w-1,m+w\rangle\) の boundary family のみである。
今回必要な true narrow は \(m\ge w+2\) なので、R24-N02 の
\(h=1,t=w-1,w=t+1,m\ge w+2\) 枝がちょうど合成箇所になる。
\(m=w+1\) の七点や全 ratio cover machinery は本 N4 の第一行には不要。
この family 自体の任意体・全 multiplicity 証明の監査完了は、別担当の結論に委ねる。

五支持の具体的な健全性確認として \(\langle229,230,309,387\rangle\) の
\(xyv^6\) を actual 最大 order DP から独立計算した。
weight は 2781、次数 8、実 order 9、長い表示は \(z^9\)。
一変数で割った三つの divisor の実 order は全て 7 であり、type IV を捨てられない。
記録は `xyv_support_control.json`。これは紙上の支持分類を置換する証明ではなく具体的検査である。

本稿で未解決に残すのは、別担当が扱う boundary family と高次行との合成だけである。
一般 primitive 第一行の \(U\) 構成・無界幅・有限 offset 残余には、未証明の内的補題を残さない。
外部標準入力 Savchev–Chen は明示的に引用して残す。
任意体への移行は、整数の支持・合同式・計数と任意体上の Gröbner 除法だけなので、
有限個の標数の計算から一般標数への外挿もない。
