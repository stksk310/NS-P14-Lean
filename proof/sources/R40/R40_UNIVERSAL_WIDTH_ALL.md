# R40-WALL：任意生成元数の幅側全域閉鎖

## 1. 主定理

**定理 WALL.** $e\ge8$、$q=e-2$ とする。任意の体 $k$ と任意の真正な正規化 source

\[
\Gamma=\langle m,m+da_1,\ldots,m+da_q,m+du\rangle,
\quad 0<a_1<\cdots<a_q<u<m,\quad
\gcd(m,d)=\gcd(u,a_1,\ldots,a_q)=1
\]

に対し、P14 はすべてのホモロジー次数で成立する。

これは **$m>u$ の全域**を、$e$ に上限なく同時に閉じる定理である。
R39 の $e\le12$ 全域閉鎖と合わせれば、幅側はすべての生成元数について閉じる。
ただし $m\le u$ の小欠損域や U-open をこの定理から閉じたことにはならない。

新しい中核は有限コアの列挙ではなく、Artin lex の総最大変数分布を正確に telescope する恒等式と、欠落数による短い原証明である。
新規性は固定 R39 入力に対するもので、文献上の優先性を主張しない。

以下、範囲外の二項係数は 0 とし、$i\ge1$ を扱う。第 0 行は双方 1。
source の次数を超える行は 0 である。

## 2. 継承した同じ source の移行

R39 の整数 Artin コア $Q=C/(x,v)$、長さ $P=P_C$、Cayley 質量 $W$、実 endpoint socle $R$ について

\[
\beta_i(G_\Gamma)\le b_i(Q)+P\binom q{i-1}
                           +R\binom{q+1}{i-1},                 \tag{2.1}
\]

\[
P\le W,\qquad R\le W-u,\qquad
R\le u\max(H_x-2,0).                                         \tag{2.2}
\]

比較先の実効幅 $V=\min(du,m-1)\ge u$ は

\[
\beta_i(G_{\widetilde\Gamma})\ge
F_i^{\min}(u)=i\binom u{i+1}
     +\min\left\{\binom u{i-1},\binom ui\right\}.              \tag{2.3}
\]

これらの原証明は固定 R39 `lanes/core/R39_ACTUAL_SOURCE_CORE_TRANSFER.md` §§1–4 にある。
(2.1) は実全射の kernel–Tor を含むため、商に対する Betti 単調性を必要としない。

## 3. 欠落 prefix 補題と密な residue 集合

\[
t=u-1-q
\]

を内部 offset の欠落数とする。

**補題 3.1（欠落 prefix）.** $Q_n\ne0$ なら $n\le t+1$。したがって $H_x\le t$。

証明：非零基底元を表す内部 word の prefix 和を、mod $u$ で考える。
長さ $\ell\ge2$ の部分 word の residue が既存 offset $a$ なら、その offset 和は $a+cu$、$0\le c\le\ell-1$ であり、整数コアで

\[
\text{その word}=x^{\ell-c-1}v^c y_a.
\]

$\ell\ge2$ なので $x$ または $v$ が現れ、$Q$ では消える。
residue が 0 の場合も、offset は $cu$、$1\le c\le\ell-1$ なので $x^{\ell-c}v^c$ となり消える。
よって長さ $2,\ldots,n$ の prefix residue は全て欠落 offset でなければならない。
二つが同じなら、その間の非空部分 word は residue 0 となる。長さ 1 の内部 offset が 0 になることもないので、これも不可能である。
したがって $n-1$ 個の相異なる欠落が必要であり、$n-1\le t$。
正次数の基底の第一座標 $L=n-\lceil b/u\rceil\le n-1$ から $H_x\le t$。□

**補題 3.2（密度）.** $0\le t\le q$ なら

\[
W=q+1+2t,\qquad P\le q+1+2t,\qquad R\le t.                  \tag{3.1}
\]

証明：巡回群 $\mathbb Z/u\mathbb Z$ 内の $A=\{0,a_1,\ldots,a_q\}$ は $q+1$ 元を持つ。
$2(q+1)>u=q+t+1$ なので任意 residue $r$ について $A\cap(r-A)\ne\varnothing$。
したがって全 residue は長さ高々 2 で到達する。既存の $q$ 個は最短長 1、欠落 $t$ 個は最短長 2、零は 0。
よって $W=1+q+2t$、残りは (2.2) による。□

特に $t\le2$ なら補題 3.1 と (2.2) から **実 source の $R=0$** である。
これはコアだけの反射不変量を実 source に無条件移す議論ではない。

## 4. Artin lex の正確な telescope

$Q$ は $q$ 変数上の標準次数付き Artin quotient、$h_0=1,h_1=q$ とする。
$L\subset T=k[y_1,\ldots,y_q]$ を同じ全 Hilbert 関数を持つ lex ideal とする。
各次数 $d$ の standard monomial は辞書順最小の $h_d$ 個である。
$S_j(d)$ を、それらのうち最初の $j$ 変数だけで supported なものの数と置く。
従って $S_0(d)=0$（$d>0$）、$S_q(d)=h_d$、$S_j(1)=j$。

最大変数が $j$ の次数 $d$ の極小生成元数を $g_j(d)$ とする。
lex ideal の stability により、shadow 内で最大変数 $j$ の単項式と、前次数の ideal 内で最大変数 $\le j$ の単項式は、$y_j$ の乗法・除去で一対一に対応する。
したがって全単項式数の同じ二項係数が差で消え、

\[
g_j(d)=S_j(d-1)-S_j(d)+S_{j-1}(d).                           \tag{4.1}
\]

Artin 性により高次数で $S_j(d)=0$。全 $d\ge2$ について (4.1) を足すと

\[
\boxed{\sum_{d\ge2}g_j(d)=j+\sum_{d\ge2}S_{j-1}(d).}       \tag{4.2}
\]

任意標数 BHP 上界と EK 公式により

\[
\begin{aligned}
b_i(Q)&\le b_i(T/L)\\
&=i\binom{q+1}{i+1}
 +\sum_{d\ge2}\sum_{j=1}^q S_{j-1}(d)\binom{j-1}{i-1}\\
&\le i\binom{q+1}{i+1}+K\binom{q-1}{i-1},                  \tag{4.3}
\end{aligned}
\]

\[
K:=\sum_{d\ge2}\sum_{j=1}^q S_{j-1}(d).                    \tag{4.4}
\]

第一項の恒等式 $\sum_{j=1}^q j\binom{j-1}{i-1}=i\binom{q+1}{i+1}$ は $j\binom{j-1}{i-1}=i\binom ji$ と hockey-stick による。
すべての行に同じ lex ideal の同じ全極小生成元を用いている。

## 5. 追加 lex 生成元の質量を $t$ だけで制御する

密な範囲 $t\le q$ では

\[
\sum_{d\ge2}h_d=P-1-q\le2t.                               \tag{5.1}
\]

$r\le q$ を $\binom{r+1}{2}\ge2t$ を満たす整数とする。
任意 $d\ge2$ で $\binom{d+r-1}{d}\ge\binom{r+1}{2}\ge h_d$ なので、次数 $d$ の lex standard は末尾の $r$ 変数だけに supported である。
全直接除数が standard に入る次数 $d+1$ の子も、その同じ $r$ 変数だけに supported である。
もし子に外側変数があれば、別の変数を除いた親にも外側変数が残る。子がその一変数の冪なら、その親自体が外側変数を持つ。いずれも矛盾する。

この子の数を $M_d(h_d)$ と記す。最大変数 $j$ の子から $y_j$ を除く対応で

\[
M_d(h_d)=\sum_{j=1}^q S_j(d),\qquad
M_d(h_d)-h_d=\sum_{j=1}^q S_{j-1}(d).                       \tag{5.2}
\]

子と親の incidence に、削除する変数の子での指数を重みとして与える。
各子の総重みは $d+1$、固定された親の全候補子への総重みは $d+r$ なので

\[
M_d(h_d)-h_d\le\frac{r-1}{d+1}h_d
                         \le\frac{r-1}{3}h_d.
\]

(5.1)、(5.2) より

\[
\boxed{K\le\frac{2t(r-1)}3.}                               \tag{5.3}
\]

これは整数の集合を有理数重みで数えた不等式であり、基礎体内の除法ではない。
任意体、有限体、標数 2 に同じく適用できる。

## 6. 密な幅の全 Betti 行

$q\ge4$、$2\le t\le q$ を扱う。$B_i=i\binom{q+1}{i+1}$ と置く。
(2.1)、(3.1)、(4.3) により

\[
\beta_i(G)\le B_i+K\binom{q-1}{i-1}
 +(q+1+2t)\binom q{i-1}+R\binom{q+1}{i-1}.                  \tag{6.1}
\]

### 6.1 欠落 $t=2$

$r=3$ を選べるので $K\le8/3$。$K$ は整数だから $K\le2$。補題 3.1 より $R=0$。
$u=q+3$ の target は、その正の最小項を落としても

\[
i\binom{q+3}{i+1}
=B_i+2(q+1)\binom q{i-1}+i\binom{q+1}{i-1}.
\]

従って target と (6.1) の差は少なくとも

\[
(q-3)\binom q{i-1}+i\binom{q+1}{i-1}
                    -2\binom{q-1}{i-1}\ge0,                 \tag{6.2}
\]

なぜなら $q-3\ge1$、$i\ge1$ で、二つの正項はそれぞれ一つの $\binom{q-1}{i-1}$ を支払うからである。

### 6.2 欠落 $t=3$

$r=3$ なので $K\le4$、$R\le3$。Pascal/Vandermonde 展開の最初の二増分を残すと

\[
i\binom{q+4}{i+1}-B_i
\ge3(q+1)\binom q{i-1}+3i\binom{q+1}{i-1}.
\]

差は少なくとも

\[
(2q-4)\binom q{i-1}+(3i-3)\binom{q+1}{i-1}
                   -4\binom{q-1}{i-1}\ge0,                  \tag{6.3}
\]

$q\ge4$、$i\ge1$ による。

### 6.3 欠落 $4\le t\le q$

$\binom{t+1}{2}\ge2t$ なので $r=t$ を使い、$K\le2t(t-1)/3$。
一般の Vandermonde 展開から

\[
i\binom{q+t+1}{i+1}-B_i
\ge t(q+1)\binom q{i-1}+i\binom t2\binom{q+1}{i-1}.
\]

$R\le t$ を使うと差は少なくとも

\[
\bigl((t-1)(q+1)-2t\bigr)\binom q{i-1}
 +\left(i\binom t2-t\right)\binom{q+1}{i-1}
 -K\binom{q-1}{i-1}.                                      \tag{6.4}
\]

$i\binom t2-t\ge t(t-3)/2\ge0$ と二項係数の単調性により、(6.4) は

\[
\left((t-1)(q+1)-2t+\frac{t(t-3)}2
                         -\frac{2t(t-1)}3\right)\binom q{i-1}
\]

以上である。
$q\ge t$ なら丸括弧は

\[
\frac{5t^2-17t-6}{6}+(t-1)(q-t)>0.                         \tag{6.5}
\]

実際 $t=z+4$、$q=t+v$、$z,v\ge0$ と置けば、6倍した式は

\[
5z^2+23z+6+6zv+18v,
\]

という非負係数多項式で、定数項は正である。
この整数多項式恒等式が無限の $q,t$ の符号を証明する。有限サンプル点の外挿ではない。

### 6.4 欠落 $t=0,1$

$t=0$、すなわち $u=e-1$ は R39 の算術最小幅定理で閉じる。
$t=1$、すなわち $u=e$ は `R40_UNIVERSAL_ONE_GAP.md` の普遍双フォーム定理 WOG で閉じる。
以上により **任意 $q\ge4$、$q+1\le u\le2q+1$** が全体・全行で閉じた。

## 7. 全幅への接続

$e\ge8$、$q\ge6$ とする。$u\le2q+1$ は §6 で閉じる。
$u\ge2q+2$ では

\[
2q+2\ge q+2+\lceil\sqrt{q-1}\rceil
       =e+\lceil\sqrt{e-3}\rceil
\]

なので、継承 R39-W1 の幅 tail に入る。
実際 $\lceil\sqrt{q-1}\rceil\le q$ は $q\ge1$ に対する整数不等式である。
二つの範囲に間隙はない。これで WALL が証明された。

13・14 生成元の 4,200 コア証明書は、この普遍結論とは別経路で具体的有限補集合を独立に認証する。
普遍定理の証明にその 4,200 件の成功を外挿していない。

## 8. 標準依存と論理的な限界

既知の BHP/EK の任意標数での仮定・式は `R40_WIDTH_COMPLETION.md` §5 の一次研究文献で再確認した。
継承依存は actual-source transfer、Cayley/Pareto bounds、算術 target、W1、および低生成元数の既済閉鎖である。
本版で初めて示した数学的機構は、欠落 prefix、Artin lex telescope、追加 Hilbert 質量による全行補償、密な幅の普遍原証明である。

この結果は一般 P14 の完全証明ではない。正規化後 $m\le u$ かつ小欠損の領域は依然として別の問題である。
未知の spectral differential rank を既知扱いせず、追加 torsion head の U-open 不等式を証明したとも主張しない。
