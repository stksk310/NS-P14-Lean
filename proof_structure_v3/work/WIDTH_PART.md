# Part V　narrow-width 側の全域閉鎖

## V.0　適用範囲と共通入力

本 Part では物理的な真正狭幅 \(w=du\le m-2\)、すなわち \(m\ge du+2\) を固定する。
正規化は actual source の表示
\[
\Gamma=\langle m,m+da_1,\ldots,m+da_q,m+du\rangle,
\quad q=e-2,\quad0<a_1<\cdots<a_q<u,
\quad \gcd(m,d)=\gcd(u,a_1,\ldots,a_q)=1
\]
の座標を取る操作であり、source を別の半群へ置き換える操作ではない。
内部 offset が \(q\) 個あるので \(u\ge q+1=e-1\)。体 \(k\) は任意、\(d\ge1\)。
比較先は常に actual interval completion であり、実効幅はここでは \(V=du\ge u\) である。

Part IV の `E_CORE,E_COORD,E_KERNEL,E_BOUNDS,E_TRANSFER,E_TWO,E_ARTIN` を用いる。
特に \(P=P_C=\dim Q_C\)、\(R=\dim_k(0:_G(x,v))\)、元の向きの \(H_x\) に対し
\[
P\le W:=1+\sum_{r=0}^{u-1}\ell_r,\qquad
R\le\min\{W-u,\ u\max(H_x-2,0)\},                         \tag{V.1}
\]
\[
\beta_i(G)\le b_i(Q_C)+P\binom q{i-1}+R\binom{q+1}{i-1}. \tag{V.2}
\]
ここには実全射 \(Q_C\twoheadrightarrow Q_G\) の核の長さ \(P_C-P_G\) による Tor 補償が入る。
商の Betti 単調性、\(P_C=P_G\)、反射した別 source の \(R\) はいずれも使わない。
`I_TARGET` より、全正行について
\[
F_i^{\min}(u)=i\binom u{i+1}
 +\min\!\left\{\binom u{i-1},\binom ui\right\}
 \le F_i(m,V)=\beta_i(G_{\widetilde\Gamma}).               \tag{V.3}
\]
これは実 target の下界の幅単調性であり、比較先を正規化幅の仮想半群へ変える主張ではない。
二項係数は範囲外で0とする。第0行は双方1、source は \(i>e\) で0である。

## V.1　五生成元以上：端の二幅 `W_EDGE`

**主張・役割。** \(e\ge5\) の \(u=q+1,q+2\) を、後続の密幅評価と分離して全行閉じる。

\(u=q+1=e-1\) は完全な算術列 source である。算術列公式の補正項は
\(i\le c\) なら \((c+1-i)\binom u{i-1}\)、\(i>c\) なら \((i-c)\binom ui\)、\(1\le c\le u\)。
どちらも \(i\binom ui\) 以下なので \(\beta_i(G)\le i\binom{u+1}{i+1}\)。
\(d=1\) では source=target、\(d\ge2\) では \(V\ge2u\ge u+1\) なので target 第一項が払う。
この Part の \(m\ge du+2\) では、より広い V02 の境界 \(m=e\) を別途使う必要はない。

\(u=q+2=e\) では欠落 offset を \(h\in\{1,\ldots,u-1\}\) とする。
\(B=\{0,\ldots,u\}\setminus\{h\}\) に対し、次数 \(n\) の core 商の基底は
\(nB\setminus((n-1)B\cup((n-1)B+u))\)。したがって
\[
h_0=1,\ h_1=q,\ Q_{C,\ge3}=0,\quad
Q_{C,2}=\begin{cases}k(2,h)\oplus k(2,h+u),&2\le h\le u-2,\\
k(2,u+1),&h=1,\\ k(2,u-1),&h=u-1.\end{cases}             \tag{V.4}
\]
内部欠落では \(B+B=[0,2u]\)、端欠落でも次次数の端点表示が \(3B\) を覆うことで従う。
各基底点を元の向きで見ると \(L=n-\lceil b/u\rceil\le1\) なので \(H_x\le1\)、従って \(R=0\)。
反射は \(h=u-1\) の **core 基底** の記述にだけ用い、actual \(R\) には用いない。

内部欠落では \(r=h-1,s=u-h-1\)、\(r+s=q\)、\(r,s\ge1\) と置く。
次数1の二ブロックの積は、それぞれ \(a\mapsto h-a\)、\(a\mapsto h+u-a\) の置換フォーム。
次数1から2への Koszul 微分は、非零行ごとに一つの \(\pm1\) 列を選べるので
\[
\rho_i=2\binom q{i-1}-\binom s{i-1-r}-\binom r{i-1-s},
\quad b_i=i\binom{q+1}{i+1}-2\binom q{i-1}+T_i,
\quad T_i=\binom{s+1}{i-r}+\binom{r+1}{i-s}.              \tag{V.5}
\]
整数行列の単位 minor を使うため標数2も含む。二つの集合族への包含単射により
\(T_i\le\min\{\binom{q+2}{i-1},\binom{q+2}i\}\)（V02 §13.2 の衝突一個の移動を保持）。
\(P=q+3\)、\(R=0\) を \(V.2\) に入れると \(V.3\) との差は正確にこの最小値から \(T_i\) を引いたもの。
端欠落では単一置換フォームにより \(P=q+2\)、\(\rho_i=\binom q{i-1}\ (1\le i\le q)\)、
\(\rho_{q+1}=0\) であり
\[
\beta_i(G)\le i\binom{q+2}{i+1}
 +\mathbf1_{i=q}+\mathbf1_{i=q+1}.                      \tag{V.6}
\]
二指示関数はそれぞれの行で target の最小補正1以上が払う。特に上端 \(i=q+1\) の項を落とさない。
**完全証明。** V02 §13.2、\(W5\)–\(W12\)。次節では \(t=u-1-q\ge2\) だけが残る。

## V.2　密な幅の一つの差 `W_DENSE`

**資源部分の量化。** \(q\ge3\)、\(0\le t=u-1-q\le q\)。閉鎖部分は \(q\ge4\)、\(2\le t\le q\)。
非零内部標準語の長さ \(n\) について、長さ2以上の prefix 剰余は欠落 offset であり、互いに異なる。
既存 offset または0なら端点表示、prefix の重複なら零和部分語が生じるからである。
従って \(n\le t+1\)、元の向きの \(H_x\le t\)。また \(|A|=q+1>u/2\) だから \(2A\) は全群であり
\[
W=q+1+2t,\quad P\le q+1+2t,\quad R\le t,
\qquad t\le2\Longrightarrow R=0.                       \tag{V.7}
\]
同じ **全 Hilbert 関数** の一つの lex 商に BHP–EK を適用する。
\(S_j(n)\) を最初の \(j\) 変数内の次数 \(n\) 標準単項式数とすると、極小生成元の telescope から
\[
b_i(Q_C)\le i\binom{q+1}{i+1}+K\binom{q-1}{i-1},
\qquad K=\sum_{n\ge2}\sum_{j=1}^qS_{j-1}(n).            \tag{V.8}
\]
\(\binom{r+1}2\ge2t\)、\(r\le q\) なら高次標準語は末尾 \(r\) 変数に支持され、
親子への指数重み incidence により \(K\le\sum_{n\ge2}(r-1)h_n/(n+1)\le2t(r-1)/3\)。
これは整数集合の有理重み計数であり、体内で除法していない。

読者が追うべき target 第一項との差を一つに固定する：
\[
A_i=\binom{q-1}{i-1},\quad C_i=\binom q{i-1},\quad B_i=\binom{q+1}{i-1},
\quad\mathscr D_i=i\!\left[\binom{q+t+1}{i+1}-\binom{q+1}{i+1}\right]
 -(q+1+2t)C_i-RB_i-KA_i.                               \tag{V.9}
\]
Vandermonde の \(j=1,2\) 項は \(t(q+1)C_i\)、\(i\binom t2B_i\) である。

- \(t=2\)：\(r=3\)、整数性で \(K\le2\)、\(R=0\)。
  \(\mathscr D_i\ge(q-3)C_i+iB_i-2A_i\ge0\)（\(q\ge4\)）。
- \(t=3\)：\(r=3\)、\(K\le4\)、\(R\le3\)。
  \(\mathscr D_i\ge(2q-4)C_i+(3i-3)B_i-4A_i\ge0\)。
- \(4\le t\le q\)：\(r=t\)、\(K\le2t(t-1)/3\)、\(R\le t\)、\(B_i\ge C_i\ge A_i\) より
  \[
  \mathscr D_i\ge\left[\frac{5t^2-17t-6}{6}+(t-1)(q-t)\right]C_i\ge0.
  \]
  \(t=4+z,q=t+v\)、\(z,v\ge0\) とすると括弧の6倍は \(5z^2+23z+6+6zv+18v>0\)。

全 \(1\le i\le e=q+2\) で有効であり、target の追加補正は不要。
これと `W_EDGE` により \(e\ge6\)、\(e-1\le u\le2e-3\) が閉じる。
**完全証明・補強。** V02 §13.3 \(W13\)–\(W16\)、LATER_READABILITY_AUDIT §3。

## V.3　疎な幅と全高次行 `W_SPARSE`

**範囲。** \(e\ge6\)、\(u\ge2e-2\)、全 \(d\ge1,m\ge du+2\)。
\(a=e-1\)、\(s=\lceil a/2\rceil=\lfloor e/2\rfloor\)、\(A=\{0,a_1,\ldots,a_q\}\)。
Kneser の stabilizer \(H\) と \(A+H\) の coset 数 \(c\) に対し、全群に達する前は
\(c\ge2,c|H|\ge a\)、従って増分は \((c-1)|H|\ge\lceil a/2\rceil\)。合成数 \(u\) も含む。
\[
|nA|\ge\min\{u,a+(n-1)s\},\quad
W\le B(u):=u+\sum_{j\ge0}(u-a-sj)_+.                   \tag{V.10}
\]
\(\Delta=u-a=sk+b\)、\(0\le b<s\) と置けば
\[
B=u+\frac{\Delta^2}{2s}+\frac\Delta2+\frac{b(s-b)}{2s}
 \le B_*:=u+\frac{\Delta^2}{2s}+\frac\Delta2+\frac{\lfloor s^2/4\rfloor}{2s},
\quad B\le\frac{u^2}{e-1}.                             \tag{V.11}
\]
最後の差の \(2a\) 倍は \(s(2s-a)k^2+ask+2(2s-a)kb+2b^2\ge0\)。
`E_ARTIN,E_TRANSFER` に \(P\le B,R\le B-u\) を代入すると
\[
\beta_1\le\frac{e+3}{3}B-u+\frac{e(e-1)}6,
\quad\beta_1\le\frac{e+5}{4}B-u+\frac{(e-1)e(e+1)}{24},
\quad\beta_i\le U_i:=B\binom ei-u\binom{e-1}{i-1}-\binom{e-1}{i+1}\quad(2\le i\le e).
                                                                    \tag{V.12}
\]
第一行の target 下界は \(\binom u2+1\)。\(z=u-(2e-2)\ge0\) として、第二上界の \(B=B_*\) との差は

| \(e\) | \(B_*\) | target 下界との差 |
|---:|---|---|
|6| \((u^2-u+12)/6\) | \(z^2/24+43z/24+1/2\) |
|7| \((u^2-3u+20)/6\) | \(2z+1\) |
|8| \((u^2-2u+25)/8\) | \(3z^2/32+63z/16+211/32\) |
|9| \((u^2-4u+36)/8\) | \(z^2/16+17z/4+29/4\) |

\(e\ge10\) は第一上界と \(B\le u^2/(e-1)\) を使い、差は
\[
\frac{(e-1)(e-10)}2+1+\frac{4e-33}{6}z+\frac{e-9}{6(e-1)}z^2>0. \tag{V.13}
\]
第二行には
\(2\binom u3-U_2\ge u[2u^2-(3e+6)u+6e-2]/6+\binom{e-1}3\) を使う。
\(e=8+v,u=2e-2+z\) で中括弧は \(2v^2+5vz+16v+2z^2+26z+18>0\)。
\(e=7,u=12+z\) では \(2z^2+21z+4>0\)、\(e=6,u\ge10\) では差は
\((u-10)(u-3)(u+1)/3\) 以上である。

全高次行への論理の橋を明示する。\(2\le i\le e\) に対し
\[
\mathcal T_i(u)=\frac{i\binom u{i+1}}{\binom ei}
 +\frac{ui}{e}+\frac{(e-i)(e-i-1)}{e(i+1)}.             \tag{V.14}
\]
\(i\binom u{i+1}\ge U_i\) と \(\mathcal T_i(u)\ge B(u)\) は同値である。
\(\mathcal T_i(e)=e-1+i/e\)、幅増分は \(i\binom ui/\binom ei+i/e\)。
\(u\ge e\) では隣接比 \((u-i)/(e-i)\ge1\ (i<e)\) だから基点も全増分も \(i\) とともに増加し、
\(\mathcal T_i(u)\ge\mathcal T_2(u)\ge B(u)\)。上端 \(i=e\) も含めて全高次行が従う。
**完全証明。** V02 §13.4 \(W17\)–\(W21\)。

## V.4　五生成元の残余 `W_FIVE` と閉鎖 `W_CLOSE`

\(e=5,q=3\)、\(u\ge4\)。\(u=4,5\) は `W_EDGE`、残りを以下で処理する。
三変数 Artin 商について \(b_1\le P+2,b_3\le P-1\)、rank-zero Euler 特性より \(b_2\le2P\)。
従って
\[
(\beta_2,\beta_3,\beta_4,\beta_5)
 \le(5P+4R,\ 4P+6R-1,\ P+4R,\ R).                   \tag{V.15}
\]
\(u=6\) は \(V.7\) で \(P\le8,R=0\)、整数性で \(b_1\le8\)、従って \(\beta_1\le16\)。
\(u=7\) は \(P\le10,R\le3,b_1\le10\)。\(R=0\) なら \(\beta_1\le20\)。
\(R>0\) なら元の向きの \(H_x\ge3\) より \(Q_{C,4}\ne0\)、従って \(\tau=\sum_{n\ge3}h_n\ge1\) であり
\(b_1\le6+2(P-4)/3-\tau/6<10\)。整数性で \(b_1\le9\)、\(\beta_1\le22\)。
この改善は \(R>0\) の分岐だけに用いる。

| \(u\) | 第2–5行の上界 | \(F_2^{\min},F_3^{\min},F_4^{\min},F_5^{\min}\) |
|---:|---|---|
|6| \((40,31,8,0)\) | \((46,60,39,11)\) |
|7| \((62,57,22,3)\) | \((77,126,119,56)\) |

\(u\ge8\) では、四元集合 \(A=\{0,a,b,c\}\) の Kneser 増分が3未満になる唯一の構造は
\[
u=2h,\quad A=\{0,t,h,t+h\},\quad h\ge4,\quad0<t<h,\quad\gcd(t,h)=1. \tag{V.16}
\]
これは stabilizer の位数と coset 数がともに2のときである（antipodal 分岐）。
それ以外では \(W\le B_3(u)=u+\sum_{j\ge0}(u-4-3j)_+\)、かつ
\[
B_3(3j),B_3(3j+1),B_3(3j+2)
 =\tfrac12(3j^2+j+2,\ 3j^2+3j+2,\ 3j^2+5j+4).        \tag{V.17}
\]
\(\beta_1\le\lfloor5B_3/2-u+5\rfloor\)。床を取る前の target 差は順に
\((3j^2+j-26)/4,(3j^2+3j-22)/4,(3j^2+5j-24)/4\)。
\(u\ge9\) の各該当 \(j\ge3\) で正、\(u=8\) は \(B_3=13\) から床付き上界29で閉じる。
antipodal では直接の基底から
\[
Q_C=k[y,z,w]/(yz,z^2,zw,(y,w)^h),\quad
P=\binom{h+1}2+1,\quad b_1=h+4,\quad W=h^2-h+2.        \tag{V.18}
\]
次数 \(n<h\) の \((y,w)\) 語は offset が相異なり、\(\gcd(t,h)=1\) が次数間の剰余を分離する。
次数 \(h\) は端点と \(z\) で全て消える。第一行の target 差は \((h^2+h-12)/2\ge0\)。
両構造共通の高次行には \(P\le u^2/4,R\le u^2/4-u\) を \(V.15\) へ入れる。
第2行の差は \(u(4u-7)(u-8)/12\ge0\)。残りの粗い上界は
\((\beta_3,\beta_4,\beta_5)\le(5u^2/2,5u^2/4,u^2/4)\)。
\(u=8\) で target 第一項 \((210,224,140)\) が払い、
\(\binom uk/u^2\) は固定 \(k=4,5,6\) で増加するので全 \(u\ge8\) へ延びる。

**`W_CLOSE`。** \(e\ge6\)：\(u=e-1,e\) と \(e+1\le u\le2e-3\)、\(u\ge2e-2\) が連続して全域を覆う。
\(e=5\)：\(u=4,5,6,7\)、\(u\ge8\) の二構造が全域を覆う。
これで全 \(e\ge5,d\ge1,m\ge du+2,i\ge0\) に actual interval 比較が成立する。
**完全証明。** V02 §13.5 \(W22\)–\(W25\)。有限 offset core 証書は依存しない。

## V.5　四生成元の距離・標準語 `N_DISTANCE,N_WORDS`

以下は \(q=2\)、\(0<a<b<u\)、\(u\ge3\)、\(\gcd(a,b,u)=\gcd(m,d)=1\)、\(m\ge du+2\)。
\(Q_C=k[y,z]/I_C\) は単項式 Artin 商であり、標準語の downset を \(D\subset\mathbb N^2\)、
\(P=|D|\)、\(\sigma=\dim\operatorname{soc}Q_C\) と書く。同次数・同 offset の内部語は一意である。
`E_TWO` により
\[
(\beta_1,\beta_2,\beta_3,\beta_4)
 \le(P+\sigma+1+R,\ 2P+\sigma+3R,\ P+3R,\ R).          \tag{V.19}
\]

**`N_DISTANCE`。** \(A=\{0,a,b\}\subset\mathbb Z/u\mathbb Z\) に Kneser を適用する。
\(H=\operatorname{Stab}(nA)\) による商で反復すると \(|nA|\ge n|A+H|-(n-1)|H|\)。
非自明な真部分群では \(|A+H|\ge2|H|\)、自明なら \(|A|=3\) なので
\[
|nA|\ge\min(u,2n+1),\quad W\le1+\lfloor u^2/4\rfloor,
\quad\binom{\sigma+1}2\le P\le W,\quad\sigma\le u-1.  \tag{V.20}
\]
socle 極大点を第一座標昇順に並べると \((\alpha_i,\beta_i)\ge(i,\sigma-1-i)\)。
従って全次数 \(\sigma-1\) の単項式と約数が標準である、という強い antichain 事実も保持する。

**`N_WORDS`。** 純冪は gcd による周期関係、または \(qa\equiv b\pmod u\) の置換関係で
次数 \(u-1\) までに端点表示を持つ。従って純標準語長は \(u-2\) 以下。
混合標準語は零和部分列を持たない。長さ \(u/2\) 超なら Savchev–Chen で unit 倍後の
正代表を \(1,c\)（\(c\ge2\)）、個数を \(R_0,T_0\ge1\) とできる。
\(Y_\alpha^c=x^{c-1-k}Y_\beta v^k\) の端点表示により \(R_0<c\)、総和条件は \(R_0+cT_0\le u-1\)。
従って \(2(R_0+T_0)\le(u-1)+(c-1-(c-2))=u\)、矛盾。
\(h=\lfloor u/2\rfloor\) として
\[
st>0\Longrightarrow s+t\le h,\quad s+t\le u-2\ ((s,t)\in D),
\quad P\le2u-3+\binom h2,\quad H_x\le u-3.              \tag{V.21}
\]
特に \(u=3,4\) は元の actual \(R=0\)。unit は有限群の列にだけ作用し、source を反射しない。
**完全証明。** V02 §§14.2–14.3 \(N6\)–\(N13\)。Kneser と Savchev–Chen は主依存として残る。

## V.6　四生成元の全高次行 `N_HIGH`

\(V.19\)–\(V.20\) より \(U_2=5u^2/4-2u+4,U_3=u^2-3u+4,U_4=u^2/4-u+1\) が上界。
actual target の非減少な下界は
\[
L_2(V)=2\binom V3+V\ (V\ge3),\quad
L_3(V)=3\binom V4+\binom V2\ (V\ge5),\quad L_4(V)=4\binom V5.
\]
\(u=6+z\) で \(12(L_2-U_2)=4z^3+45z^2+152z+108>0\)。
\(u=5+z\) で \(8(L_3-U_3)=z^4+14z^3+67z^2+134z+88>0\)、
\(60(L_4-U_4)=2z^5+30z^4+170z^3+435z^2+458z+105>0\)。
\(u=5\) の第2行だけは床を保持し、\(W\le7,R\le2,\sigma\le4\) より \(\beta_2\le24<25\)。
\(u=4\) は \(P\le5,\sigma\le2,R=0\) で \((\beta_2,\beta_3,\beta_4)\le(12,5,0)\)。
\(V=4\) の target 最小値は \((12,7,0)\)、\(V\ge5\) は上記下界が払う。
\(u=3\) は \(Q_C=k[y,z]/(y,z)^2\)、\((P,\sigma,R)=(3,2,0)\)。\(d=1\) は source=target、
\(d\ge2\) は \(V\ge6\) が上界 \((8,3,0)\) を払う。これで全 \(u\ge3\)、第2–4行が成立。
**完全証明。** V02 §14.4 \(N14\)–\(N18\)。この高次行証明は196組証書に依存しない。

## V.7　N4 第一行の紙上置換 `N_FIRST`

core には三つの端点関係
\[
y^b=x^{b-a}z^a,\quad z^{u-a}=y^{u-b}v^{b-a},\quad
y^{u-b}z^a=x^{u-b}v^a                                  \tag{V.22}
\]
がある。\(k_0=u-b+a\in[2,u-1]\)、\(h=\lfloor u/2\rfloor\) とし、
\(E_h(k_0)=\binom{h-k_0+2}2\)（\(k_0\le h\)）、それ以外0と定める。
純軸は \(1+(b-1)+(u-a-1)=2u-k_0-1\) 点以下。
第三関係の倍数は \(s=u-b+i,t=a+j\)、\(i+j\le h-k_0\) なので混合三角形から正確に \(E_h(k_0)\) 点を除く。
従って
\[
P\le2u-k_0-1+\binom h2-E_h(k_0)
 \le2u-h-2+\binom h2,\qquad\sigma\le\min(h+1,k_0).     \tag{V.23}
\]
後半は、混合 socle の第一指数が相異なることと、\(\sigma\ge k_0+1\) なら
antichain 事実により禁止語 \(y^{u-b}z^a\) が標準になることから従う。
\(V.19\) より \(\beta_1\le\binom h2+u+1+\lfloor u^2/4\rfloor\)。
\(L_1(u)=\binom u2+1\) との差は \(u=2h\) で \(h(h-5)/2\)、\(u=2h+1\) で \((h^2-3h-2)/2\)。
従って **全 \(u\ge9\)** が閉じる。\(u=5\) も \(P\le7,\sigma\le3,H_x\le2\) で \(R=0\)、上界11。
**完全証明・補強。** N4_PAPER_REDUCTION_JA §§1–2 \(P1\)–\(P7\)、LATER_READABILITY_AUDIT §5。

## V.8　幅6–8と幅3・4の小場合 `N_SMALL`

下記の \(R\) はすべて元の向きの \(V.1\) で評価する。
一方向の指数が \(c-1\) 以下の downset の antichain は高々 \(c\) 点であることを使う。

- \(u=6\)：\(P\le10,\sigma\le4,H_x\le3\)。\(H_x\le2\) なら上界15。
  \(H_x=3\) の標準語は次数4・offset 6以下の純 \(y^4\) に限られ、\(a=1,b=5\)。
  \(yz=xv,y^5=x^4z,z^5=yv^4\) から \(P\le9,\sigma\le2,R\le4\)、上界16。
- \(u=7\)：\(R\le6\)、上界 \(23-k_0-E_3(k_0)+\min(4,k_0)\)。
  \(k_0=2,3\) は20,22、\(k_0\ge5\) は \(27-k_0\le22\)。残る \(k_0=4\) は
  \((a,b)=(1,4),(2,5),(3,6)\)。外側はそれぞれ \(z^2=yv\)、\(y^2=xz\) と純冪関係で
  \(P\le7,\sigma\le2\)、上界16。中央は \(yz=xv\) で \(P\le9,\sigma\le2\)、上界18。
- \(u=8\)：\(R\le9\)、上界 \(31-k_0-E_4(k_0)+\min(5,k_0)\)。
  \(k_0=2,3\) は25,28、\(k_0\ge7\) は \(36-k_0\le29\)。
  \(k_0=4\) は gcd 条件により \((1,5),(3,7)\)。前者は \(y^5=x^4z,z^5=xyv^3\)、後者は
  \(y^5=x^3zv,z^5=yv^4\) なので純軸9点、混合6点中1点禁止で \(P\le14,\sigma\le4\)、上界28。
  \(k_0=5\) は \((1,4),(2,5),(3,6),(4,7)\)：順に \(z^2=xv,z^2=yv,y^2=xz,y^2=xv\)。
  \(P\le9,\sigma\le2\)、上界21。
  \(k_0=6\) は \((1,3),(3,5),(5,7)\)：外側は一辺3の strip と純冪関係で \(P\le14,\sigma\le3\)、上界27。
  中央は \(yz=xv\) で \(P\le9,\sigma\le2\)、上界21。
- \(u=3\)：唯一の \((1,2)\)。\(d=1\) は source=target、\(d\ge2\) は上界6を \(V\ge6\) の容量16以上が払う。
- \(u=4\)：\(P\le5,\sigma\le2,R=0\)。\(d\ge2\) は上界8を \(V\ge8\) の容量29以上が払う。
  \(d=1,(a,b)=(1,2),(2,3)\) は \(D\subset\{1,y,z,yz\}\) より \(P+\sigma\le5\)、上界6。
  残る \(d=1,(a,b)=(1,3)\) は次節へ渡す。

各数値は \(L_1(6)=16,L_1(7)=22,L_1(8)=29\) 以下。
有限 offset core の exact 値を参照せず、関係式と downset の包含だけで示した上界である。
**完全証明。** N4_PAPER_REDUCTION_JA §§3–6。有限の場合分けは保持し、196組証書は除外する。

## V.9　幅4の全 multiplicity の Gröbner 証明 `N_WIDTH4`

**厳密な範囲。** \(d=1,u=4,(a,b)=(1,3),m\ge6\)。\(m=4Q+\rho\)、\(0\le\rho<4\)。
内部重み \(\mathrm{wt}(y)=1,\mathrm{wt}(z)=2,\mathrm{wt}(x)=\mathrm{wt}(v)=0\) を先に比較する大域順序を使う。
core の四関係 \(y^3-x^2z,yz-xv,xz^2-y^2v,z^3-yv^2\) の候補先頭 ideal は
\(J_0=(y^3,yz,xz^2,z^3)\)。標準列は自由列 \(1,y,y^2,z\) と \(x\) 指数0の制限列 \(z^2\)。
自由列の offset 剰余が相異なり、制限列と自由列の同 offset 表示は次数が異なるので像は独立。
停止除算により、この四関係は core の完全 Gröbner 基底である。

基点 \(b\) の次数・offset を \((c,n)\)、短い語を \(x^Lv^Kb\) とする。
長さが \(j\ge1\) 増える自由 anchor の剰余と座標を
\[
r_j=(n-jm)\bmod4,\quad\kappa_j=(jm+r_j-n)/4,
\quad\lambda(0),\lambda(1),\lambda(2),\lambda(3)=(0,1,2,1),
\quad\Delta_j=\lambda(r_j)-c-\kappa_j-j
\]
とすると、offset と長さの等式を解いた **両座標** は
\[
K'=K-\kappa_j,\qquad L'=L+c+j+\kappa_j-\lambda(r_j)=L-\Delta_j. \tag{V.24}
\]
従って非負の長い表示が存在する必要十分条件は \(K\ge\kappa_j,L\ge\Delta_j\)。
\[
4\Delta_j=(4\lambda(r_j)-r_j)-(4c-n)-j(m+4)\le6-(m+4)<0. \tag{V.25}
\]
制限 anchor \(z^2\) による競合は \(K\ge\kappa_j+1\) を必要とし、自由 anchor の条件に含まれる。
\(\kappa_j\) は \(j\) について非減少なので \(j=1\) が正確な消滅閾値となる：
\[
\theta_n=\max\{\lceil(m-n)/4\rceil,0\},\quad
J=J_0+(bv^{\theta_n}:b=1,y,y^2,z,z^2).                  \tag{V.26}
\]
禁止された標準語は長い表示を持つので actual 接錐で0。
非禁止語は最大分解長が元の次数に等しく、同次数の異なる標準語の actual weight が相異なるので像は独立。
従って kernel に非禁止余りはなく **\(\operatorname{in}(I_G)=J\)**。
\(J\) の各極小生成元を先頭項に持つ同次式を選び、停止除算によりそれらが \(I_G\) を生成する。
これで任意体上 \(\beta_1(G)=\mu(I_G)\le\mu(J)\) を得る。
\(m=6\) は \(J=(v^2,zv,z^2,yz,y^2v,y^3)\)、上界6、target9。

| \(m>6\) の \(\rho\) | \((\theta_0,\theta_1,\theta_2,\theta_3,\theta_6)\) | \(\mu(J)\) | \(F_1(m,4)\) |
|---:|---|---:|---:|
|0| \((Q,Q,Q,Q,Q-1)\) |6|7|
|1| \((Q+1,Q,Q,Q,Q-1)\) |8|10|
|2| \((Q+1,Q+1,Q,Q,Q-1)\) |8|9|
|3| \((Q+1,Q+1,Q+1,Q,Q)\) |6|8|

これは全 \(m\ge6\) の記号的四剰余証明である。**完全証明・補強。** V02 §14.6 \(N23\)–\(N28\)、LATER_READABILITY_AUDIT §2。

## V.10　四生成元の閉鎖 `N_CLOSE` と Part VI への接続

第一行は \(u=3,4\) を `N_SMALL,N_WIDTH4`、\(u=5\) と \(u\ge9\) を `N_FIRST`、
\(u=6,7,8\) を `N_SMALL` が覆う。第2–4行は全幅の `N_HIGH`、第0行は双方1、第4行超は source が0。
従って全 \(e=4,d\ge1,m\ge du+2,i\ge0\) に actual interval 比較が成立する。
Part VI は `W_CLOSE,N_CLOSE` を \(e\le3\) と ordinary 側に接続するだけでよい。
本 Part の主依存に196組 core 証書、83組・665比較・5 tail、ナヴィ増分補題は入らない。
Kneser、Savchev–Chen、共通端点の actual 核補償、幅6–8の紙上場合分け、幅4の全 \(m\) 証明は残る。
監査は数学的読解と厳密算術の補助照合であり、Lean kernel による形式認証はまだない。
