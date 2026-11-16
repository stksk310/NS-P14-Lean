# R39-W1/W2：生成元数に上限を置かない幅の定理

この証明は旧 R39 の保持された数学的導出を再構成したものであり、旧原文の hash 一致は主張しない。有限点の数値比較を無限領域へ外挿しない。整数多項式恒等式と符号を以下で証明し、checker がその恒等式を独立した疎多項式演算で検査する。

## 1. 定理

`R39_ACTUAL_SOURCE_CORE_TRANSFER.md` の正規化された真正 source を取り、e=q+2>=8、m>u とする。任意の体、任意の d>=1、gcd(m,d)=1 に対して

\[
\boxed{u\ge e+\lceil\sqrt{e-3}\rceil\quad\Longrightarrow\quad
\beta_i(G_\Gamma)\le\beta_i(G_{\widetilde\Gamma})\ \text{for all }i.}
\tag{W1}
\]

第一行だけなら

\[
\boxed{u\ge e+3\quad\Longrightarrow\quad
\beta_1(G_\Gamma)\le\beta_1(G_{\widetilde\Gamma}).}
\tag{W2}
\]

特に e=11 では u>=14、e=12 では u>=15 を閉じる。一般 e の残る有限幅は e-1<=u<=e+ceil(sqrt(e-3))-1 で、その内部 offset 候補総数は

\[
\sum_{u=e-1}^{e+c_0-1}\binom{u-1}{e-2}
=\binom{e+c_0-1}{e-1},\qquad c_0=\lceil\sqrt{e-3}\rceil.
\tag{1.1}
\]

これは m>u 領域の還元定理である。m<=u の一般 P14 をここから結論しない。

## 2. Cayley 質量の上界

a=e-1、s=ceil(a/2)=floor(e/2) と置く。mod u の集合 A={0,a_1,...,a_q} は a 個の元を持ち、全巡回群を生成する。Kneser の標準和集合定理を次の形で用いる。

\[
|X+Y|\ge|X+H|+|Y+H|-|H|,
\quad H=\operatorname{Stab}(X+Y).
\tag{2.1}
\]

(n+1)A が真部分集合のとき、H は真部分群。A+H は t 個の H-coset を含み、A が群を生成するため t>=2。また t|H|>=a。従って

\[
|(n+1)A|\ge|nA|+(t-1)|H|\ge|nA|+\lceil a/2\rceil.
\]

よって |nA|>=min(u,a+(n-1)s), n>=1。零元を含むため nA は長さ高々 n の到達集合であり、最短語長の和は

\[
W=u+\sum_{n\ge1}(u-|nA|)
\le B(u):=u+\sum_{j\ge0}(u-a-sj)_+.
\tag{2.2}
\]

ここで u=a+st+r、t>=0、0<=r<s と書くと

\[
B(u)=u+(t+1)(st/2+r),\qquad B(u+s)-B(u)=u+2s-a.
\tag{2.3}
\]

また

\[
2a\left(\frac{u^2}{a}-B(u)\right)
=s(2s-a)t^2+as t+2(2s-a)tr+2r^2\ge0.
\tag{2.4}
\]

従って B(u)<=u^2/(e-1)。この stabilizer 議論は u が合成数でも有効である。

## 3. 同じ source の上界

端点定理の実 kernel–Tor 補償と P_C<=W、R<=W-u を適用すると

\[
\beta_1(G)\le\frac{e+3}{3}B(u)-u+\frac{e(e-1)}6=:U_1(u),
\tag{3.1}
\]

\[
\beta_i(G)\le B(u)\binom ei-u\binom{e-1}{i-1}
-\binom{e-1}{i+1}=:U_i(u),\quad 2\le i\le e.
\tag{3.2}
\]

最後の控除は **C(e-1,i+1)** である。C(e,i+1) への置換は行わない。完備化の容量は同文書の F_i^min(u) 以上である。

## 4. 第一行：u>=e+3

D(u)=C(u,2)+1-U_1(u) と置く。最初の s 個の幅を u=a+k、4<=k<=s+3 と書く。この範囲では z=(k-s)_+、B=a+2k+z だから

\[
6D=2a(k-3)+3k^2-13k+6-2(a+4)z.
\tag{4.1}
\]

k=4 で 6D=2(a+1)>0。k を1増す差は、break より前では 2a+6k-10、break 以後では 6k-18 であり、いずれも正。k=s から s+1 への差も後者で覆う。したがって s 個の連続 anchor 全てで D>0。

(2.3) から、s 刻みの差は次の形になる。

\[
6(D(u+s)-D(u))=
\begin{cases}
(2s-8)u+3s^2+3s,&a=2s,\\
(2s-6)u+3s^2-s-6,&a=2s-1.
\end{cases}
\tag{4.2}
\]

e>=8 なので s>=4、両式は正。連続 s anchor と s 刻みの帰納法が全 u>=e+3 を覆う。これで W2 を得る。

## 5. 短い初期区間：e+c_0<=u<=e+s+1

c_0=ceil(sqrt(e-3)) は 3<=c_0<=s-1 を満たす。後半は e=2s なら (s-1)^2-(e-3)=(s-2)^2>=0、e=2s+1 なら (s-1)^2-(e-3)=(s-1)(s-3)>=0 から従う。

u=e+c、c_0<=c<=s+1、z=(c+1-s)_+ と置く。この区間全体で

\[
B(u)=e+2c+1+z.
\tag{5.1}
\]

### 第二行

u>=3 なので F_2^min(u)=2*C(u,3)+u。直接展開すると

\[
F_2^{\min}(e+c)-U_2(e+c)
=-e^2+(c^2+3)e+2\binom c3-1-z\binom e2.
\tag{5.2}
\]

c=c_0 では z=0、c_0^2>=e-3 より右辺>=2*C(c_0,3)-1>=1。
c を1増す差は、z が変わらないとき e(2c+1)+c(c-1)>0、z が1増すときはさらに C(e,2) を引いたもの。後者の開始位置 c=s-1 での値は

\[
3s^2-4s+2\quad(e=2s),\qquad 3s^2-4s+1\quad(e=2s+1),
\]

であり、s>=4 で正。その後はさらに増える。従って第二行はこの全区間で閉じる。

### 第三行以降

Vandermonde 恒等式と (3.2) から、3<=i<=e で

\[
\begin{aligned}
i\binom{e+c}{i+1}-U_i(e+c)
={}&\binom ei\left((i-2)c-2+\frac{i(c+1)}e-z\right)\\
&+i\sum_{j=2}^{c}\binom cj\binom e{i+1-j}.
\end{aligned}
\tag{5.3}
\]

括弧内は c-2-z 以上。z=0 なら c-2>=1、z>0 なら c-2-z=s-3>=1。よって正であり、非負の完備化補正項を使わなくても支払える。i=e も同式に含まれる。

## 6. 残る全幅：u>=e+s+2

e+s+2=ceil((3e+3)/2)。まず第二行で (2.4) を代入すると

\[
2\binom u3-U_2(u)
\ge\frac u6\{2u^2-(3e+6)u+6e-2\}+\binom{e-1}3.
\tag{6.1}
\]

u=e+s+2+t, t>=0 と書くと、中括弧は

\[
\begin{cases}
2t^2+(6s+2)t+6s-6,&e=2s,\\
2t^2+(6s+3)t+3s-5,&e=2s+1.
\end{cases}
\tag{6.2}
\]

全係数が正、または非負で定数が正なので、第二行は ordinary 部分だけで支払える。

高次行への移行も明示する。2<=i<=e に対し

\[
T_i(u)=\frac{i\binom u{i+1}}{\binom ei}
+\frac{ui}{e}+\frac{(e-i)(e-i-1)}{e(i+1)}.
\]

T_i(u)>=B(u) は ordinary 部分 i*C(u,i+1)>=U_i(u) と同値である。基点では T_i(e)=e-1+i/e。整数 u の増分は

\[
T_i(u+1)-T_i(u)=\frac{i\binom ui}{\binom ei}+\frac{i}{e}.
\tag{6.3}
\]

u>=e のとき C(u,i)/C(e,i) は i とともに非減少である。実際、隣り合う比は (u-i)/(e-i)>=1 for i<e。従って (6.3) も i とともに増え、基点と帰納法から T_i(u)>=T_2(u) for all u>=e, i>=2。第二行の (6.1) が T_2>=B を与えるので、全高次行も閉じる。i=e-1 から i=e への比では分母 e-i=1 であり、端点を除外していない。

第4節が第一行を、第5–6節が全高次行を覆うので W1 が証明された。i=0 は両辺1、i>e は source の Betti 数が0である。

## 7. 依存と診断の意味

使用した外部標準結果は Kneser の和集合定理、初期イデアルへの Betti 上半連続性、および固定入力で監査済みの算術列接錐公式である。Kneser の正確な形と使用箇所は第2節に記した。実 source への移行、socle、Artin incidence、低次数 unit minor は同梱の一般端点証明に全て記載した。

`verify_universal_width_tail.py` の有限 anchor は実装上の診断である。無限 e,u の結論は上記の全パラメータ恒等式と符号から得られ、有限探索件数による外挿ではない。全判定は明示的例外を用い、Python の -O で消える assert に依存しない。
