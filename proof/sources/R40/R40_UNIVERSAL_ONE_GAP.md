# R40-WOG：任意生成元数の一欠落幅定理

## 1. 結論と入力境界

**定理 WOG.** $e=q+2\ge5$、$u=e$、$m>u$ とし、任意の体 $k$ 上で

\[
\Gamma=\langle m,\ m+da\ (1\le a\le u-1,\ a\ne h),\ m+du\rangle,
\qquad 1\le h\le u-1,\quad d\ge1,\quad\gcd(m,d)=1
\]

とする。この真正な $e$ 生成元数値半群の接錐は、その区間完備化の接錐に対し、
すべての Betti 行で P14 を満たす。標数 2 を含むすべての体に同じ証明が適用される。

以下は $q,m,d,h$ に上限を置かない原証明である。有限証明書は $q=11,12$ の適用を独立再生するために添付するが、定理の普遍性を有限計算から外挿しない。
「新規」は固定 R39 入力に対する研究上の進歩であり、文献上の優先性を意味しない。

使用する継承定理は R39 `lanes/core/R39_ACTUAL_SOURCE_CORE_TRANSFER.md` §§1–4 の次の式に限定する。
整数 Artin コア $Q=C/(x,v)$、内部環 $T=k[y_1,\ldots,y_q]$ に対し

\[
\beta_i(G_\Gamma)\le b_i^T(Q)+P_C\binom q{i-1}
                       +\widehat R\binom{q+1}{i-1},             \tag{1}
\]

\[
P_C=\dim Q,\qquad
\widehat R=\min\{W-u,\ u\max(H_x-2,0)\}.
\]

これは実全射 $Q\twoheadrightarrow G/(x,v)G$ の kernel–Tor を保持した、同じ source に対する移行式である。
任意商の Betti 単調性も、接錐の Cohen–Macaulay 性も仮定しない。
比較先の実効幅 $V=\min(du,m-1)\ge u$ の全行容量は

\[
F_i^{\min}(u)=i\binom u{i+1}
       +\min\left\{\binom u{i-1},\binom ui\right\}.           \tag{2}
\]

最小生成性は $m>u$ と $\gcd(m,d)=1$ から従う。実際、生成元 offset $a\le u$ が長さ $\ell\ge2$、offset 和 $B\ge0$ の語に分解すると、

\[
(\ell-1)m=d(a-B),\qquad \ell-1=jd,\quad a-B=jm\ge m>u
\]

という矛盾を得る。残った offsets と $u$ の gcd は 1 なので半群は数値半群である。

## 2. 一欠落コアの全基底と実 socle

\[
C_{\mathbb Z}=\mathbb Z[s^u,s^{u-a}t^a\ (a\ne h),t^u],
\qquad Q_{\mathbb Z}=C_{\mathbb Z}/(s^u,t^u).
\]

基底元を次数・offset $(n,b)$ で記す。$Q_0=\mathbb Z$、$Q_1$ の基底は $a\in\{1,\ldots,u-1\}\setminus\{h\}$ の $y_a$ であり、その数は $q$ である。

内部の欠落 $2\le h\le u-2$ では

\[
Q_2=\mathbb Z z_-\oplus\mathbb Z z_+,
\qquad z_-=(2,h),\quad z_+=(2,h+u),\qquad Q_{\ge3}=0.       \tag{3}
\]

証明：$B=\{0,1,\ldots,u\}\setminus\{h\}$ とすると、$B\cup(B+u)$ に欠ける候補は $h,h+u$ だけである。
これらはそれぞれ $1+(h-1)$、$(u-1)+(h+1)$ と表されるので $B+B=[0,2u]$。
次次数では $(B+B)\cup(B+B+u)=[0,3u]$ がすべてを消す。標準次数付き代数なので $Q_3=0$ から全高次数が消える。

端の欠落 $h=1$ では $B+B=\{0\}\cup[2,2u]$ となり、

\[
Q_2=\mathbb Z(2,u+1),\qquad Q_{\ge3}=0.                    \tag{4}
\]

$h=u-1$ では反射で $Q_2=\mathbb Z(2,u-1)$。この反射は整数コアの記述にのみ使う。
元の向きの各基底点の Pareto 第一座標は $L=n-\lceil b/u\rceil\le1$ である。
したがって元の source に対し $H_x\le1$、$\widehat R=0$ を直接得る。
さらに欠落剰余だけが最短長 2、他の非零剰余は最短長 1 なので $W=q+3$。
内部欠落では $P_C=q+3$、端欠落では $P_C=q+2$ である。

## 3. 双フォームの原単位 minor

内部欠落の場合、$V=Q_1=U\oplus W'$ と書き、

\[
U=\langle y_a:1\le a<h\rangle,\quad r=h-1,\qquad
W'=\langle y_a:h<a<u\rangle,\quad s=u-h-1,\qquad r+s=q.
\]

乗法は

\[
y_a y_b=\begin{cases}
z_-&a,b<h,\ a+b=h,\\
z_+&a,b>h,\ a+b=h+u,\\
0&\text{otherwise}.
\end{cases}                                                   \tag{5}
\]

各ブロックの双線型フォームは、$a\mapsto h-a$、$a\mapsto h+u-a$ の置換行列そのものである。
平方項も係数 1 であり、偏極による係数 2 は現れない。

次数 1 から 2 へ行く実 Koszul 微分を

\[
D_i:V\otimes\bigwedge^iV\longrightarrow
   (kz_-\oplus kz_+)\otimes\bigwedge^{i-1}V
\]

とする。各 column $y_a\otimes e_I$ は、$a$ のフォーム双対が $I$ に存在するとき一つの $\pm1$、それ以外は 0 を持つ。
したがって非零 row ごとに一つの column を選べば、元の整数行列の対角 $\pm1$ minor を得る。

$z_-\otimes e_J$ が非零 row である条件は $U\not\subseteq J$ である。
実際 $v\in U\setminus J$ を選び、フォーム双対 $v^*\in U$ に対して $v^*\otimes e_{J\cup\{v\}}$ を使えば、その column は求める row だけに $\pm1$ を持つ。
逆に $U\subseteq J$ なら、その row へ来る column は存在しない。第二ブロックも同様である。
よって**すべての体で正確に**

\[
R_i:=\operatorname{rank}D_i
=2\binom q{i-1}-\binom s{i-1-r}-\binom r{i-1-s}.              \tag{6}
\]

rank の上界は零 row の個数、下界は同じ元行列の単位 minor による。スペクトル系列の収束や有理数 rank に頼っていない。

次数 0 から 1 への Koszul 微分は $\bigwedge^iV\to V\otimes\bigwedge^{i-1}V$ であり、各 $i$ 元集合の最小要素を選ぶ原単位 minor により rank は $\binom qi$。
この微分と $D_i$ は異なる内部次数にあるため、それぞれの rank が全微分の rank に加算される。
従って $1\le i\le q$ に対し

\[
b_i(Q)=(q+2)\binom qi-\binom q{i+1}-R_i-R_{i+1}.
\]

Pascal 恒等式で整理すると、$i\ge1$（範囲外の $b_i=0$ を含む）について

\[
\boxed{b_i(Q)=i\binom{q+1}{i+1}-2\binom q{i-1}+T_i},
\qquad T_i=\binom{s+1}{i-r}+\binom{r+1}{i-s}.                \tag{7}
\]

ここで二項係数は下添字が範囲外なら 0 とする。$b_0(Q)=1$ は別途保持し、(7) を $i=0$ に適用しない。

## 4. 二つの包含写像による全行支払い

**組合せ補題.** $r,s\ge1$、$q=r+s\ge3$、$i\ge1$ なら

\[
T_i\le\binom{q+2}{i},\qquad T_i\le\binom{q+2}{i-1}.        \tag{8}
\]

第一不等式：互いに素な集合 $U,W'$（大きさ $r,s$）と追加二点 $a,b$ を取る。
第一項を $U\cup D$, $D\subseteq W'\cup\{a\}$, $|D|=i-r$ に、第二項を $W'\cup E$, $E\subseteq U\cup\{b\}$, $|E|=i-s$ に写す。
同じ族内は単射で、二つの族の共通像は $i=q$ の $U\cup W'$ だけである。
この一つの重複の第二コピーを

\[
(U\setminus\{u_0\})\cup(W'\setminus\{w_0\})\cup\{a,b\}
\]

に移す。この像はどちらの元の族にも属さない。したがって $i$ 元集合全体への単射が得られる。

第二不等式：$k=q+1-i$ と置く。$k<0$ では左辺は 0。$k\ge0$ では

\[
T_i=\binom{r+1}{k}+\binom{s+1}{k}.
\]

互いに素な $A,B$ の大きさを $r+1,s+1$ とし、それぞれ二点 $a_1,a_2$、$b_1,b_2$ を固定する。
一方の $k$ 元部分集合へ反対側の固定二点を加え、$A\cup B$ の $k+2$ 元集合に写す。
二つの族が衝突するのは $k=2$、像 $\{a_1,a_2,b_1,b_2\}$ の一箇所だけである。
$q\ge3$ なので少なくとも一方のブロックに三点あり、その側から三点、他方から一点を取った未使用の像へ第二コピーを移す。
こうして単射が得られ、$\binom{q+2}{k+2}=\binom{q+2}{i-1}$ が上界となる。

(1)、(7)、$P_C=q+3$、$\widehat R=0$ より

\[
\beta_i(G_\Gamma)\le i\binom{q+1}{i+1}
             +(q+1)\binom q{i-1}+T_i.
\]

$i\binom{q+1}{i}=(q+1)\binom q{i-1}$ を用いると、容量 (2) とこの上界との差は正確に

\[
\min\left\{\binom{q+2}{i-1},\binom{q+2}{i}\right\}-T_i\ge0.
\]

これで内部欠落の全行が閉じる。

## 5. 端欠落の全行

$h=1$ または $h=u-1$ では、全 $q$ 変数上の非退化置換フォームが一つだけある。
同じ原単位 minor 議論で

\[
R_i=\binom q{i-1}\quad(1\le i\le q),\qquad R_{q+1}=0.
\]

$P_C=q+2$、$\widehat R=0$ を (1) に代入して整理すれば

\[
\beta_i(G_\Gamma)\le i\binom{q+2}{i+1}
                +\mathbf1_{i=q}+\mathbf1_{i=q+1}.              \tag{9}
\]

第 $q+1$ 行の指示関数も必要である。この行では移行上界は $P_C=q+2$ となる。
二つの指示関数は異なる行にあり、当該行で容量 (2) の最小項は 1 以上なので支払われる。
第 0 行は双方 1、source の射影次元を超える行は source が 0 である。
以上で定理 WOG が全パラメータ、全体、全行について証明された。

## 6. 計算証明書との対応

`produce_width.py` は各 $q=11,12$ の全欠落位置に対し、上の実 $D_i$ の疎整数行列を構成し、その全 entry 列の SHA-256、全非零 row を覆う原単位 minor の row/column/sign、閉式 rank を記録する。
`consume_width.py` は producer を import せず、組合せ wedge と実コア乗法から行列を再構成する。
minor の各 selected column が元行列で一つの $\pm1$ しか持たないこと、全非零 row をちょうど一度覆うこと、実際の隣接微分の積が整数で 0 になることを確認する。
したがって有限記録も標数を特定していない。証明書に記録した rank を任意体で正確な rank とする根拠は原単位 minor と零 row の一致である。
