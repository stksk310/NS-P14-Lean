## Part IV：narrow-width 側の共通端点理論

この Part は actual な接錐を整数コアの商として保持し、その全 Betti 行を端点資源で評価する。
ordinary 側の Apéry 商・cut・lex 比較には依存しない。一般の半群から以下の表示への正規化は全域合成で行う。
以下の共通仮定を **(EH)** と呼ぶ。
\[
k\text{ は任意の体},\quad q\ge2,\quad
0<a_1<\cdots<a_q<u<m,\quad d\ge1,\qquad
\gcd(a_1,\ldots,a_q,u)=\gcd(m,d)=1.                 \tag{EH}
\]
\(\Gamma=\langle m,m+da_1,\ldots,m+da_q,m+du\rangle\)、
\(G=\operatorname{gr}_{\mathfrak m}k[[t^\Gamma]]\)、\(e=q+2\) とする。
必要なのは \(u<m\) であり、\(du<m\) は仮定しない。
範囲外の二項係数と負の添字の Betti 数は 0 とする。

### IV.1 `E_CORE`：actual 接錐への単項式全射

**主張・役割。** (EH) の全パラメータについて、\(\Gamma\) は表示された最小生成系を持つ数値半群であり、
\[
S=k[x,y_1,\ldots,y_q,v],\quad E=k[x,v],\quad T=k[y_1,\ldots,y_q],
\qquad C=k[s,st^{a_1},\ldots,st^{a_q},st^u]
\]
から actual な次数付き環全射 \(\phi:C\twoheadrightarrow G\) がある。
ここで \(x=s,y_j=st^{a_j},v=st^u\) はすべて次数 1 とする。
\(h\in\Gamma\) の最大分解長を \(\nu(h)\) とすると、
\[
\phi(s^nt^B)=
\begin{cases}(t^{nm+dB})^*\in G_n,&\nu(nm+dB)=n,\\
0,&\nu(nm+dB)>n.
\end{cases}                                                   \tag{IV.1}
\]
**証明の核心。** offset \(a\le u\) の生成元が長さ \(l\ge2\)、offset 和 \(B\ge0\) の語なら、
\((l-1)m=d(a-B)\) より \(l-1=jd,a-B=jm\ge m>u\) となり矛盾する。
二つの gcd 条件は全生成元の gcd が 1 であることも与える。
\(G_n\) の基底は \(\nu(h)=n\) の数値指数 \(h\) で区別され、最大長表示が全射性を与える。
固定した次数 \(n\) の異なる offset \(B\) は異なる \(nm+dB\) を与えるので、核は \(C\) の単項式基底の一部で張られる。
**次への接続。** この全射の核を端点座標で正確に記述し、別の数値半群への source の置換を避ける。
**完全証明。** [V02 §12.1](/workspace/NS-P14-Lean/proof_integrated_v2/NS_P14_INTEGRATED_PROOF_JA.md:815)、(E1)–(E2)。

### IV.2 `E_COORD`：有限な整数コアと \(E\)-加群座標

**主張。** \(0\le r<u\)、\(\epsilon_r=[r>0]\) と置く。コア単項式は一意に
\[
B=r+uK,\qquad n=L+K+\epsilon_r,\qquad L,K\ge0            \tag{IV.2}
\]
と表される。\(x,v\) はそれぞれ \(L,K\) を 1 増やす。
\(|\alpha|\le u-1\) の内部語について
\[
B_\alpha=\sum_j\alpha_ja_j,\quad r=B_\alpha\bmod u,\quad
K=\lfloor B_\alpha/u\rfloor,\quad L=|\alpha|-K-\epsilon_r   \tag{IV.3}
\]
を作り、その \(x^Lv^K\) で生成する単項式イデアルを \(M_r\subset E\) とする。この有限リストで
\[
C\simeq\bigoplus_{r=0}^{u-1}M_r[\epsilon_r,r],\qquad
M_r\ne0,\quad M_0=E,\qquad
H_x:=\max_{r,(L,K)\in\operatorname{Min}M_r}L\le u-2.       \tag{IV.4}
\]
括弧は次数・offset の移動である。この直和は **\(E\)-加群の直和**であり、環の直積分解ではない。
**証明の核心。** 内部因子が \(u\) 個あれば、最初の \(u\) 因子の prefix offset を mod \(u\) で比べる。
同じ剰余の二つの prefix の間の非空語は長さ \(l\)、offset \(cu\)、\(1\le c\le l-1\) を持つ。
これを \(x^{l-c}v^c\) に換える操作は次数と offset を保ち、内部因子数を減らす。
反復で (IV.3) を得る。gcd 条件により全剰余へ内部語で到達でき、最短経路の長さは \(u-1\) 以下である。
非零剰余の極小点では \(L+K\le u-2\)、剰余 0 の極小点は \((0,0)\) のみである。
**次への接続。** 端点の単項式イデアルで全競合を表現できる。内部変数の乗法は剰余成分を移す。
**完全証明。** [V02 §12.2](/workspace/NS-P14-Lean/proof_integrated_v2/NS_P14_INTEGRATED_PROOF_JA.md:849)、(E3)–(E5)。

### IV.3 `E_KERNEL`：長い表示との全競合と actual 核

**主張。** 次数・offset \((n,B)\) に対するすべての長い表示は、ちょうど
\[
(n,B)\longmapsto(n+jd,B-jm),\qquad j\ge1                 \tag{IV.5}
\]
のうち右辺がコアに属するものから成る。長い側の剰余 \(r\)、短い側の剰余 \(s\) を
\(r+jm=s+cu\) で結ぶと、長い側の極小点 \((L,K)\in\operatorname{Min}M_r\) が禁止する領域の始点は
\[
\left(\max\{0,L-jd-c+\epsilon_r-\epsilon_s\},\ K+c\right).\tag{IV.6}
\]
全 \(j,r,(L,K)\) のこの点で生成するイデアルを \(T_s\subset E\) とすると、
\[
\boxed{N_s=M_s\cap T_s,\qquad
G\simeq\bigoplus_{s=0}^{u-1}M_s/N_s[\epsilon_s,s].}      \tag{IV.7}
\]
後半も \(E\)-加群同型である。\(T_s\) は競合領域であり、actual 核 \(N_s\) と同一視しない。
**証明の核心。** 数値指数の等式は \(\delta m=d(B-B')\) であり、\(\gcd(m,d)=1\) から
\(\delta=jd,B'=B-jm\) が必要十分となる。長さと offset の二等式を解くと clamp 前の (IV.6) が出る。
第一座標を 0 に切った点も、長い側へ必要な \(x\) 冪を掛ければ実現する。
\(m>u\) より \(c\ge1\) なので第二座標の切断は不要である。
競合する短い側が実際に \(C\) に属する条件が \(M_s\) との共通部分である。
**次への接続。** 無限個の \(j\) を次の停止式で有限化する。
**完全証明。** [V02 §12.3](/workspace/NS-P14-Lean/proof_integrated_v2/NS_P14_INTEGRATED_PROOF_JA.md:876)、(E6)–(E8)。

### IV.4 `E_STOP`：全競合の有限停止と端点 rank 0

**主張。** (EH) の全 \(m,d\) に対して、
\[
c-\epsilon_r+\epsilon_s\ge\lfloor jm/u\rfloor,\qquad
\max\{0,L-jd-c+\epsilon_r-\epsilon_s\}
\le\max\{0,H_x-2j\}.                                   \tag{IV.8}
\]
\(J_0=\lfloor(u-2)/2\rfloor\)、\(p=u/\gcd(m,u)\) とすると、固定した \(j\) の生成イデアル \(T_{s,j}\) により
\[
T_s=\sum_{j=1}^{J_0+p}T_{s,j},\qquad N_s=M_s\cap T_s.    \tag{IV.9}
\]
より短い停止値 \(J_0=\max\{0,\lfloor(H_x-1)/(d+\lfloor m/u\rfloor)\rfloor\}\) も使える。
**証明の核心。** \(jm=hu+t\)、\(0\le t<u\) と書き、\(r+t<u,=u,>u\) を分ければ (IV.8) を得る。
\(j>J_0\) では第一座標はすべて 0 である。\(j\) を \(j+p\) にすると、固定した \(s\) に対する \(r\) は同じで、
\(c\) が \(m/\gcd(m,u)\) 増す。従って後の生成元は前の生成元の倍数であり、(IV.9) が全競合を尽くす。
全 \(M_r\ne0\) なので各 \(T_s\) は純粋な \(v\) 冪を含む。さらに
\[
m(m+du)=(m+du)m\quad\Longrightarrow\quad
v^m=0\text{ in }G,\quad v^mM_s\subset N_s,\quad
\operatorname{rank}_E G=0.                              \tag{IV.10}
\]
\(G\) は有限生成 \(E\)-加群である。ここで \(G\) 自体の有限 \(k\)-次元性を主張してはいない。
**次への接続。** 有限生成性・rank 0 が端点 Koszul homology の Euler 等式を可能にする。
**完全証明。** [V02 §12.4](/workspace/NS-P14-Lean/proof_integrated_v2/NS_P14_INTEGRATED_PROOF_JA.md:902)、(E9)–(E11)。

### IV.5 `E_HOMOLOGY`：端点 Koszul homology の正確な三項

**主張。**
\[
Q_C=C/(x,v)C,\quad P_C=\dim_kQ_C,\qquad
Q_G=G/(x,v)G,\quad P_G=\dim_kQ_G,\qquad R=\dim_k(0:_G(x,v)).
\]
\(Q_C\) は標準次数付き \(T\)-Artin 商で、\((Q_C)_1\cong k^q\)、\((Q_C)_n=0\ (n\ge u)\) である。
その基底は全 \(\operatorname{Min}M_s\) であり、actual 商の基底はそのうち生存する点である。従って
\[
P_C=\sum_s\#\operatorname{Min}M_s,\quad
P_G=\sum_s\#\{g\in\operatorname{Min}M_s:g\notin N_s\},
\quad
R=\sum_s\#\{(L,K)\in M_s\setminus N_s:(L+1,K),(L,K+1)\in N_s\}.\tag{IV.11}
\]
\(N_s\) の極小点を \(A_0<\cdots<A_t\)、\(B_0>\cdots>B_t\) の順で並べれば、
\(E/N_s\) の両端点 socle は隣接角 \((A_{i+1}-1,B_i-1)\ (0\le i<t)\) を基底とする。
このうち \(M_s\) に入る点だけが \(R\) に寄与する。\(E/N_s\) の Artin 性は不要である。
**証明の核心。** 有限生成 \(E\)-加群の端点 Koszul homology は \((x,v)\) で殺され、有限 \(k\)-次元である。
その第 0・第 2 homology はそれぞれ \(Q_G,(0:_G(x,v))\)。Hilbert syzygy と分数体上の rank Euler 等式から
\[
\boxed{\dim_k H_\bullet(x,v;G)=(P_G,P_G+R,R).}            \tag{IV.12}
\]
すなわち \(b_0^E-b_1^E+b_2^E=\operatorname{rank}_E G=0\) を使うのであり、\(G\) の有限長 Euler 等式ではない。
**次への接続。** この正確な三項が actual 核を保持した全 Betti 行の移行に使われる。
**完全証明。** [V02 §12.5](/workspace/NS-P14-Lean/proof_integrated_v2/NS_P14_INTEGRATED_PROOF_JA.md:931)、(E12)–(E15)。

### IV.6 `E_BOUNDS`：距離和・height による \(m,d\) 一様上界

**主張。** 内部ステップ \(a_j\) による mod \(u\) の最短語長を \(\ell_r\)、\(\ell_0=0\) とし、
最短点を \((L_r,K_r)\) とする。このとき
\[
W=1+\sum_r\ell_r,\quad L_r+K_r=\ell_r-\epsilon_r,
\qquad
\boxed{P_C\le W,\quad R\le\widehat R:=\min\{W-u,\ u\max(H_x-2,0)\}.}\tag{IV.13}
\]
**\(P_C\) の証明。** 最短点は \(M_r\) の極小点である。別点に支配されれば、それより短い内部語で同じ剰余へ到達して最短性に反する。
極小点を第一座標昇順に並べれば、
その左は高々 \(L_r\) 点、右は高々 \(K_r\) 点なので、\(r\ne0\) の極小点数は高々 \(\ell_r\)。\(M_0=E\) の 1 点を加える。
**carry 相殺の証明。** \(T_s\) の極小点数を \(z_s+1\)、最小第二座標を \(\kappa_s\) とする。
純粋な \(v\) 冪があるので最初の第一座標は 0。二次元 antichain の数え上げから
\[
z_s\le A+B-\kappa_s\ ((A,B)\in T_s),\qquad
\kappa_s\ge\left\lceil\frac{m-s}{u}\right\rceil,
\quad\sum_s\left\lceil\frac{m-s}{u}\right\rceil=m.        \tag{IV.14}
\]
最後は \(m=hu+t\)、\(0\le t<u\) と書けば \(t(h+1)+(u-t)h=m\) である。
各最短点に \(j=1\) の競合を適用して始点を \((A_r,B_r)\) とすると、
\[
s_r=(r+m)\bmod u,\quad c_r=(r+m-s_r)/u,\quad
A_r\le L_r,\quad B_r=K_r+c_r,\quad \sum_rc_r=m.
\]
\(r\mapsto s_r\) が置換であるため、必要な相殺は正確に次の三行となる。
\[
\begin{aligned}
\sum_s z_s&\le\sum_r(A_r+B_r-\kappa_{s_r})\\
&\le\sum_r(L_r+K_r)+\underbrace{\sum_rc_r}_{m}
                         -\underbrace{\sum_s\kappa_s}_{\ge m}\\
&\le\sum_r(\ell_r-\epsilon_r)=W-u.
\end{aligned}                                               \tag{IV.15}
\]
\(M_s/(M_s\cap T_s)\hookrightarrow E/T_s\) の socle 単射と隣接角の計数から \(R\le\sum_sz_s\) を得る。
別に (IV.8) は全極小点の第一座標を \(0,\ldots,\max(H_x-2,0)\) に制限し、\(z_s\le\max(H_x-2,0)\) を与える。
**次への接続。** core の距離和・height の評価だけで actual source の \(R\) を支払える。\(\gcd(m,u)=1\) も Cohen–Macaulay 性も不要。
\(P_C,W,H_x,R\) はすべて上で固定した同じ向きの core と actual \(G\) に属し、反射した core の値を無条件に混用しない。
**完全証明。** [V02 §12.6](/workspace/NS-P14-Lean/proof_integrated_v2/NS_P14_INTEGRATED_PROOF_JA.md:965)、(E16)–(E18)；[後半可読性監査 §1](/workspace/NS-P14-Lean/auditability_search/LATER_READABILITY_AUDIT.md:9)。

### IV.7 `E_TRANSFER`：actual 核を補償する全行 Tor 移行

**主張。** \(b_i^T(-)=\dim_k\operatorname{Tor}_i^T(-,k)\)、\(\beta_i(G)=\dim_k\operatorname{Tor}_i^S(G,k)\) とする。
すべての \(i\ge0\) に対し
\[
\boxed{\beta_i(G)\le b_i^T(Q_C)+P_C\binom q{i-1}
                              +R\binom{q+1}{i-1}.}          \tag{IV.16}
\]
\(R\) は \(\widehat R\) に換えられる。
**証明の核心：actual quotient の補償。** 実際の完全列
\(0\to K\to Q_C\to Q_G\to0\)、\(\dim_kK=P_C-P_G\) に Tor 長完全列を適用して
\[
b_i^T(Q_G)\le b_i^T(Q_C)+b_{i-1}^T(K)
\le b_i^T(Q_C)+(P_C-P_G)\binom q{i-1}.                    \tag{IV.17}
\]
従って \(P_C=P_G\) や一般商の Betti 単調性を仮定する必要はない。
**端点から全変数へ。** actual \(G\) 上の \(K(y_1,\ldots,y_q;K(x,v;G))\) は有界二重複体である。
端点 homology を先に取る spectral sequence の第 0 行は正確に \(\operatorname{Tor}^T(Q_G,k)\) となり、
他の二行は (IV.12) と内部 Koszul 鎖群の次元で評価できる。従って
\[
\begin{aligned}
\beta_i(G)&\le b_i^T(Q_G)+(P_G+R)\binom q{i-1}+R\binom q{i-2}\\
&\le b_i^T(Q_C)+P_C\binom q{i-1}
              +R\left[\binom q{i-1}+\binom q{i-2}\right].
\end{aligned}                                               \tag{IV.18}
\]
これは (IV.16) である。各 page の項は前 page の部分商であり、退化は仮定しない。
この複体は剰余成分ごとに独立と仮定しない。内部変数の作用も actual \(G\) 上で扱う。
**次への接続。** 二内部変数では socle の正確な計数、一般 \(q\) では Artin 商の紙上評価を代入する。
**完全証明。** [V02 §12.7](/workspace/NS-P14-Lean/proof_integrated_v2/NS_P14_INTEGRATED_PROOF_JA.md:996)、(E19)–(E21)；[後半可読性監査 §7](/workspace/NS-P14-Lean/auditability_search/LATER_READABILITY_AUDIT.md:148)。

### IV.8 `E_TWO`：\(q=2\) の全四行

**主張。** (EH) に \(q=2\)、\(a_1=a,a_2=b\)、\(y_1=y,y_2=z\) を加える。
\(Q_C\) は \(k[y,z]\) の単項式 Artin 商である。\(\sigma_C=\dim_k(0:_{Q_C}(y,z))\) とすると
\[
(b_0^T(Q_C),b_1^T(Q_C),b_2^T(Q_C))=(1,\sigma_C+1,\sigma_C).
\]
**証明の核心。** 同次数の純内部語 \(y^{n-j}z^j\) の offset \(na+j(b-a)\) は相異なる。
従って生存する語の間に線形関係はない。基底点 \((r,L,K)\) に offset \(a_j\) を掛けると、
\[
r+a_j=s+cu,\qquad(r,L,K)\longmapsto
(s,L+1+\epsilon_r-c-\epsilon_s,K+c).                     \tag{IV.19}
\]
移動先が \(M_s\) の極小点ならその基底元へ、それ以外は 0 へ写る。socle は \(y,z\) の両方で 0 となる点で数えられる。
二変数 Koszul 複体の第 0・第 2 homology と有限長 Euler 等式から上の三項を得る。
(IV.16) への代入により、任意の体で
\[
\boxed{\begin{aligned}
\beta_0(G)&=1,&\beta_1(G)&\le P_C+\sigma_C+1+R,\\
\beta_2(G)&\le2P_C+\sigma_C+3R,&\beta_3(G)&\le P_C+3R,\\
\beta_4(G)&\le R,&\beta_i(G)&=0\quad(i>4).
\end{aligned}}                                               \tag{IV.20}
\]
**次への接続。** Part V の四生成元・N4 紙上置換へ渡すのはこの全四行であり、第一行だけではない。
**完全証明。** [V02 §12.8](/workspace/NS-P14-Lean/proof_integrated_v2/NS_P14_INTEGRATED_PROOF_JA.md:1020)、(E22)–(E24)。

### IV.9 `E_ARTIN`：Artin 商の親子計数と任意標数の rank 下界

**独立した主張。** 任意体上の \(T=k[y_1,\ldots,y_q]\)、\(q\ge2\) と標準次数付き Artin 商
\(A=T/I\)、\(I_1=0\) に対し、\(h_n=\dim_kA_n\)、\(P=\sum_nh_n\)、\(h_0=1,h_1=q\) と置く。
\[
\begin{aligned}
b_1^T(A)&\le q+\sum_{n\ge1}\frac{(q-1)h_n}{n+1}
\le\frac{q-1}{3}P+\frac{(q+1)(q+2)}6,\\
b_1^T(A)&\le\frac{q-1}{4}P+\frac{(q+1)^2}{4}+\frac{q-1}{12}h_2,\\
b_1^T(A)-P&\le q-1+\sum_{n\ge1}\frac{q-n-2}{n+1}h_n.
\end{aligned}                                               \tag{IV.21}
\]
特に \(q=5\) なら \(b_1^T(A)-P\le4+5+\binom62/3=14\)。
**親子計数の核心。** 初期イデアルの標準単項式集合を \(B_n\)、全直接約数が \(B_n\) に入る次数 \(n+1\) の候補を \(D_n\) とする。
子 \(y^\alpha\) から親 \(y^{\alpha-e_j}\) への重み \(\alpha_j/(n+1)\) は、子ごとに総和 1、親ごとに高々 \((n+q)/(n+1)\) なので
\(\#D_n\le(n+q)h_n/(n+1)\)。極小生成元数 \(\#D_n-h_{n+1}\) を足し、Gröbner 基底による生成元数の上界を使う。
この有理重みは整数個数の比較であり、体内での除法ではない。
**高次行。** すべての \(i\ge1\) に対し
\[
\boxed{b_i^T(A)\le P\binom qi-\binom{q+1}{i+1}.}          \tag{IV.22}
\]
係数次数 0 から 1 への Koszul 微分で、\(i\) 元集合 \(J\) の列に行 \((y_{\min J},J\setminus\{\min J\})\) を選ぶ。
\(I_1=0\) によりこれは整数行列上の \(\binom qi\) 次の符号付き単位小行列である。
従って任意体で \(\operatorname{rank}d_i\ge\binom qi\)、同様に \(\operatorname{rank}d_{i+1}\ge\binom q{i+1}\) であり、
\(b_i=P\binom qi-\operatorname{rank}d_i-\operatorname{rank}d_{i+1}\) と Pascal 恒等式を使う。\(i>q\) も両辺 0 である。
**次への接続。** (IV.21)–(IV.22) は各体で成立する上界であり、異なる標数の Betti rank の一致は要求しない。
**完全証明。** [V02 §12.9](/workspace/NS-P14-Lean/proof_integrated_v2/NS_P14_INTEGRATED_PROOF_JA.md:1050)、(E25)–(E28)。

### IV.10 `E_ROW`：Part V に渡す一般 \(q\) の全行パッケージ

**主張。** (EH) のすべてのパラメータについて、\(h_n=\dim_k(Q_C)_n\) とすると
\[
\boxed{\begin{aligned}
\beta_1(G)&\le P_C+
\left\lfloor q+\sum_{n\ge1}\frac{(q-1)h_n}{n+1}\right\rfloor+\widehat R,\\
\beta_i(G)&\le P_C\binom{q+1}i
 +\widehat R\binom{q+1}{i-1}-\binom{q+1}{i+1}
 \qquad(2\le i\le q+2).
\end{aligned}}                                               \tag{IV.23}
\]
**証明の核心。** `E_HOMOLOGY` は \((Q_C)_1\cong k^q\) と Artin 性を保証する。
\(A=Q_C,P=P_C\) として `E_ARTIN` を `E_TRANSFER` に代入し、Pascal 恒等式と \(R\le\widehat R\) を使う。
第一行は必要なら (IV.21) の \(h_2\) 付き評価または \(q=5\) の 14 上界で強める。
\(\beta_0=1\)、\(\beta_i=0\ (i>q+2)\)、上端 \(\beta_{q+2}\le\widehat R\) も明示して全行を覆う。
**次への接続。** Part V は core の \(P_C,W,H_x\) や二変数 socle を紙上評価し、actual interval の容量と比較する。
この Part 単独では target との比較を主張せず、196 組証書・ordinary 旧 §15・ナヴィ代替ルートを要求しない。
**監査状態。** V02 の紙上証明を保持し、後半可読性監査が再構成した carry の三行をここで表示した。
公刊入力自体の再査読、全パラメータの機械検証、Lean 形式認証を行ったという意味ではない。今回、この共通端点経路に真の欠落は発見していない。
**完全証明。** [V02 §12.9](/workspace/NS-P14-Lean/proof_integrated_v2/NS_P14_INTEGRATED_PROOF_JA.md:1050) (E29)、§12.5–12.7；[後半可読性監査](/workspace/NS-P14-Lean/auditability_search/LATER_READABILITY_AUDIT.md) §§1,7。
