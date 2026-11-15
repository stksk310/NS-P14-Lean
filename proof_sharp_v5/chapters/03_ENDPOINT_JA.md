# 3　端点模型と、実核を補償した一度だけの Betti 移行

本章では次の仮定を **(EH)** とする。
\[
 \begin{gathered}
 k\text{ は任意体},\quad q\ge2,\quad
 0<a_1<\cdots<a_q<u<m,\quad d\ge1,\\
 \gcd(a_1,\ldots,a_q,u)=\gcd(m,d)=1.
 \end{gathered}
\]
\[
 \begin{gathered}
 \Gamma=\langle m,m+da_1,\ldots,m+da_q,m+du\rangle,
 \quad G=\operatorname{gr}_{\mathfrak m}k[[t^\Gamma]],\\
 S=k[x,y_1,\ldots,y_q,v],\quad E=k[x,v],\quad T=k[y_1,\ldots,y_q].
 \end{gathered}
\]
すべての変数の次数は1である。\(\beta_i(G)\) は \(S\) 上、\(b_i(A)\) は \(T\) 上の total Betti 数とする。
\(\binom nj=0\) for \(j<0\) or \(j>n\)、負添字の Betti 数も0と約束する。
本章の \(d\) は dilation であり ordinary 側の multiplicity deficit ではない。
必要なのは \(u<m\) であって \(du<m\) ではない。

## E-CORE　同じ source を保つ整数コア

\[
 C=k[s,st^{a_1},\ldots,st^{a_q},st^u],
 \qquad x=s,\quad y_j=st^{a_j},\quad v=st^u
\]
と置く。\(\Gamma\) は表示された最小生成系を持つ数値半群であり、次数付き環全射
\[
 \phi:C\twoheadrightarrow G,\qquad
 s^nt^B\longmapsto
 \begin{cases}(t^{nm+dB})^*,&\nu(nm+dB)=n,\\0,&\nu(nm+dB)>n\end{cases}
 \tag{E-1}
\]
がある。ここで \(\nu(h)\) は \(h\) の最大生成元分解長である。

証明。生成元の gcd は二つの gcd 条件から1である。offset \(a\in\{0,a_1,\ldots,a_q,u\}\) の生成元が長さ \(l\ge2\)、offset 和 \(B\ge0\) の語なら
\((l-1)m=d(a-B)\)。互いに素性から \(l-1=jd\)、\(a-B=jm\) with \(j\ge1\) となり、\(a\le u<m\) に反する。したがって生成系は最小である。
\(G_n\) は \(\nu(h)=n\) の初期単項式を基底に持つ。最大長表示から (E-1) の全射性が従い、積についても最大長の定義から整合する。同じ次数 \(n\) の異なる \(B\) は異なる数値指数 \(nm+dB\) を与えるので、\(\ker\phi\) は \(C\) の単項式基底の一部で張られる。これは \(C\) の単項式性であり、一般の \(T\to C/(x,v)C\) の核が単項式であるとは主張していない。□

## E-FIBER　有限な端点座標

\(0\le r<u\)、\(\epsilon_r=[r>0]\) とする。コア単項式 \((n,B)\) に
\[
 B=r+uK,\qquad n=L+K+\epsilon_r \tag{E-2}
\]
を対応させると \(L,K\ge0\) である。実際 \(B\le nu\) だから \(n\ge\lceil B/u\rceil=K+\epsilon_r\)。\(x,v\) の作用はそれぞれ \(L,K\) を1増やす。
各 \(r\) について、この座標を持つ全コア単項式の上方閉集合を \(M_r\subset\mathbb N^2\) と書き、同時に対応する \(E\) の単項式イデアルも \(M_r\) と書く。
これは次の有限リストで生成される。
\[
 \begin{gathered}
 \alpha\in\mathbb N^q,\quad |\alpha|\le u-1,\quad B_\alpha=\sum_j\alpha_ja_j,\\
 r=B_\alpha\bmod u,\quad
 K=\lfloor B_\alpha/u\rfloor,\quad L=|\alpha|-K-\epsilon_r.
 \end{gathered}
 \tag{E-3}
\]
したがって \(E\)-加群として
\[
 C\simeq\bigoplus_{r=0}^{u-1}M_r[\epsilon_r,r],\quad
 M_r\ne0,\quad M_0=E,\quad
 H_x:=\max_{r,(L,K)\in\operatorname{Min}M_r}L\le u-2.
 \tag{E-4}
\]
これは環の直積分解ではない。

証明。内部因子が \(u\) 個以上あれば、最初の \(u\) 因子の空語を含む \(u+1\) 個の prefix offset を mod \(u\) で比較する。等しい剰余の二つの prefix の間には、長さ \(l\)、offset \(cu\) の非空語がある。\(0<a_j<u\) より \(1\le c\le l-1\) である。この語を \(x^{l-c}v^c\) に換えると次数・offset を保ったまま内部因子数が減る。反復により (E-3) を得る。
内部ステップは gcd 条件から有限群 \(\mathbb Z/u\) を生成する。負のステップは有限位数を使って非負回数に換えられ、全剰余に到達できる。最短経路は頂点を重複しないから長さは \(u-1\) 以下である。剰余0では空語が \((0,0)\) を与える。非零剰余の極小点は (E-3) のリストに含まれ、\(L+K=|\alpha|-1\le u-2\)。これで全主張と \(C\) の \(E\)-有限生成性が従う。□

## E-KERNEL　全長い表示と実際の核

次数・offset \((n,B)\) の単項式に対する長い表示は、ちょうど
\[
 (n,B)\longmapsto(n+jd,B-jm),\qquad j\ge1 \tag{E-5}
\]
のうち右辺がコアに属するものから成る。長い側の剰余を \(r\)、短い側を \(s\) として \(r+jm=s+cu\) と書く。長い側の極小点 \((L,K)\in\operatorname{Min}M_r\) は短い側で始点
\[
 \left(\max\{0,L-jd-c+\epsilon_r-\epsilon_s\},\ K+c\right) \tag{E-6}
\]
の上方閉集合を禁止する。これら全 \(j,r,(L,K)\) から生成する単項式イデアルを \(T_s\) とすれば
\[
 N_s=M_s\cap T_s,\qquad
 G\simeq\bigoplus_{s=0}^{u-1}M_s/(M_s\cap T_s)[\epsilon_s,s]
 \tag{E-7}
\]
が正確な \(E\)-加群表示である。

証明。数値指数の等式は \(\delta m=d(B-B')\) だから、\(\gcd(m,d)=1\) により \(\delta=jd,B'=B-jm\) が必要十分である。長い側の点を \((L+\lambda,K+\kappa)\)、\(\lambda,\kappa\ge0\) とすると、短い側の座標は
\[
 (L+\lambda-jd-c+\epsilon_r-\epsilon_s,\ K+\kappa+c).
\]
第一座標の非負性は \(\lambda\) を増やすことでちょうど (E-6) の clamp に置き換わる。\(m>u\) から \(c\ge1\) なので第二座標の clamp は不要である。さらに短い側が実コアに属する条件が \(M_s\) との共通部分である。(E-1) の単項式核の記述を用いれば (E-7) を得る。\(T_s\) 自体を核に置き換えてはいけない。□

全競合の有限停止も次で確認できる。\(p=u/\gcd(m,u)\)、\(J_0=\lfloor(u-2)/2\rfloor\) とすると、固定した \(j\) の競合イデアル \(T_{s,j}\) により
\[
 T_s=\sum_{j=1}^{J_0+p}T_{s,j}. \tag{E-STOP}
\]
実際 \(jm=hu+t\)、\(0\le t<u\) と書く。次の表は carry と指示関数の差をすべて尽くす。

| 条件 | \(c\) | \(s\) | \(c-\epsilon_r+\epsilon_s\) |
|---|---:|---:|---:|
| \(t=0\) | \(h\) | \(r\) | \(h\) |
| \(t>0,r+t<u,r=0\) | \(h\) | \(t\) | \(h+1\) |
| \(t>0,r+t<u,r>0\) | \(h\) | \(r+t\) | \(h\) |
| \(r+t=u\) | \(h+1\) | \(0\) | \(h\) |
| \(r+t>u\) | \(h+1\) | \(r+t-u\) | \(h+1\) |

従って
\[
 c-\epsilon_r+\epsilon_s\ge\lfloor jm/u\rfloor,\qquad
 \max\{0,L-jd-c+\epsilon_r-\epsilon_s\}
 \le\max\{0,H_x-2j\} \tag{E-8}
\]
となる。\(j>J_0\) では第一座標は0である。固定した \(s\) に対して \(j\mapsto j+p\) は長い側の \(r\) を保ち、\(c\) を \(m/\gcd(m,u)\) 増やす。従って0第一座標の範囲では後の始点は前の始点の倍数である。任意の \(j>J_0+p\) から \(p\) を反復して引けば \(J_0<j'\le J_0+p\) に達し、(E-STOP) が従う。□

明示的停止式は全競合を扱うための監査用補題である。後の端点 Euler 等式に必要な \(E\)-有限生成性は、既に (E-4) とその商表示から従っている。

## E-RESOURCES　同じ向きの core からの二つの資源

\[
 \begin{gathered}
 Q_C=C/(x,v)C,\quad P_C=\dim_k Q_C,\\
 Q_G=G/(x,v)G,\quad P_G=\dim_k Q_G,\quad
 R=\dim_k(0:_G(x,v)).
 \end{gathered}
\]
と置く。\(Q_C\) の基底は全 \(\operatorname{Min}M_r\) であり、\(Q_G\) の基底はその生存部分である。特に \(P_G\le P_C\)。\(Q_C\) は \(T\) の標準次数付き Artin 商であり、\(h_0=1,h_1=q,h_n=0\ (n\ge u)\) である。\(h_1=q\) は内部offsetが互いに異なり、端点offsetの0と \(u\) にも一致しないことによる。
内部ステップによる mod \(u\) の最短語長を \(\ell_r\)、\(\ell_0=0\) として
\[
 W=1+\sum_r\ell_r,\qquad
 \widehat R=\min\{W-u,\ u\max(H_x-2,0)\}
\]
と置く。このとき
\[
 P_C\le W,\qquad R\le\widehat R. \tag{E-9}
\]

証明。最短語の点 \((L_r,K_r)\) は \(M_r\) の極小点である。より小さい点があれば、そのコア表示から端点を除いた内部語はより短く同剰余に到達する。極小点を第一座標昇順に並べると、この点の左には高々 \(L_r\) 個、右には高々 \(K_r\) 個ある。従って \(r\ne0\) で極小点数は \(L_r+K_r+1=\ell_r\) 以下、\(r=0\) では1であり、\(P_C\le W\) を得る。また \(\ell_r\ge1\) for \(r\ne0\) だから \(W\ge u\) である。

各 \(T_s\) は純粋な \(v\) 冪を含む。実際、任意に大きい \(j\) を取り、対応する非零 \(M_r\) の極小点に (E-8) を適用すれば第一座標が0となる。\(T_s\) の極小点を
\((A_0,B_0),\ldots,(A_z,B_z)\)、\(0=A_0<\cdots<A_z\)、\(B_0>\cdots>B_z=\kappa_s\) と並べる。
\(E/T_s\) の \((x,v)\)-socle はちょうど
\((A_{j+1}-1,B_j-1)\ (0\le j<z)\) の単項式を基底に持つ。両変数倍がイデアルに入る点は隣接する二つの生成元の間のこの角に限られ、各角は実際に両変数で殺されるからである。\(E/T_s\) 全体の Artin 性は必要ない。
従って、その socle 次元を \(z_s=z\) とすれば、極小点の左右の個数を数えることにより
\[
 z_s\le A+B-\kappa_s\quad((A,B)\in T_s),\qquad
 \kappa_s\ge\left\lceil\frac{m-s}{u}\right\rceil. \tag{E-10}
\]
具体的には第 \(j\) 極小点で \(j\le A_j\)、\(z-j\le B_j-\kappa_s\) だから
\(z\le A_j+B_j-\kappa_s\)。任意のイデアル内の点はある極小点を座標ごとに支配するので、同じ上界が成り立つ。
後半は各競合の第二座標 \(K+c\) と \(c=(r+jm-s)/u\ge(m-s)/u\) による。
自然な \(E\)-線形単射 \(M_s/(M_s\cap T_s)\hookrightarrow E/T_s\) は socle にも単射を誘導するので \(R\le\sum_sz_s\)。

最短点に \(j=1\) の競合を適用し、その始点を \((A_r,B_r)\)、行先を \(s_r\) とする。すると
\[
 s_r=(r+m)\bmod u,\quad c_r=(r+m-s_r)/u,\quad
 A_r\le L_r,\quad B_r=K_r+c_r.
\]
\(r\mapsto s_r\) は置換で \(\sum_rc_r=m\)。さらに \(m=hu+t\)、\(0\le t<u\) と書けば
\(\sum_s\lceil(m-s)/u\rceil=t(h+1)+(u-t)h=m\)。従って
\[
 \begin{aligned}
 \sum_sz_s&\le\sum_r(A_r+B_r-\kappa_{s_r})\\
 &\le\sum_r(L_r+K_r)+\underbrace{\sum_rc_r}_{m}
                         -\underbrace{\sum_s\kappa_s}_{\ge m}\\
 &\le\sum_r(\ell_r-\epsilon_r)=W-u.
 \end{aligned} \tag{E-11}
\]
独立に (E-8) は \(T_s\) の極小点の第一座標を整数区間 \([0,\max(H_x-2,0)]\) に制限するので \(z_s\le\max(H_x-2,0)\)。二つを合わせて (E-9) を得る。\(\gcd(m,u)=1\) も Cohen–Macaulay 性も用いていない。□

\(P_C,W,H_x\) は固定したこの core、\(P_G,R\) は元の actual \(G\) に属する。反射した core の \(H_x\) を、元の \(R\) の上界に無条件で代入してはいけない。

## E-TOR　実核の長さを相殺する共通移行

すべての \(i\ge0\) で
\[
 \boxed{\displaystyle
 \beta_i(G)\le b_i(Q_C)+P_C\binom q{i-1}
                       +R\binom{q+1}{i-1}.} \tag{E-TOR}
\]
特に \(\beta_0(G)=1\)、\(\beta_{q+2}(G)\le R\)、\(\beta_i(G)=0\) for \(i>q+2\)。右辺の \(R\) は \(\widehat R\) に換えられる。

証明。\(C\)、従って \(G\) は \(E\)-有限生成である。数値指数の等式
\(m(m+du)=(m+du)m\) の右辺はより長い生成元表示なので \(v^m=0\) in \(G\)。従って \(\operatorname{rank}_E G=0\)。端点 Koszul homology は \((x,v)\) で殺される有限生成 \(E\)-加群であり、有限 \(k\)-次元である。第0・第2 homology の次元はそれぞれ \(P_G,R\)。\(E\) 上の有限最小自由解消に分数体を掛けて Euler 等式を取ると
\[
 \dim_kH_\bullet(x,v;G)=(P_G,P_G+R,R). \tag{E-12}
\]
ここで使ったのは \(E\)-rank の Euler 等式であり、\(G\) 自体の有限 \(k\)-次元性ではない。

実際の全射 \(Q_C\to Q_G\) の核を \(K\) とする。\(\dim_kK=P_C-P_G\ge0\) であり、Tor 長完全列と \(K\) の内部 Koszul 鎖群次元から
\[
 b_i(Q_G)\le b_i(Q_C)+(P_C-P_G)\binom q{i-1}. \tag{E-13}
\]
\(i=0\) の追加項は0である。これは任意商に対する Betti 単調性を仮定した議論ではない。
actual \(G\) 上の有界二重複体 \(K(y_1,\ldots,y_q;K(x,v;G))\) で端点 homology を先に取り、その spectral sequence を全次数 \(i\) で評価すると
\[
 \beta_i(G)\le b_i(Q_G)+(P_G+R)\binom q{i-1}+R\binom q{i-2}.
\]
第0行は正確な \(\operatorname{Tor}^T(Q_G,k)\)、他の二行は鎖群次元による上界である。有限 spectral sequence の各項は前の page の部分商だから次元は増えない。退化を仮定していない。(E-13) を代入すると \(P_C-P_G\) と \(P_G\) が相殺し、Pascal 恒等式から (E-TOR) を得る。内部作用は剰余成分を移すが、複体全体を actual \(G\) 上で作っているため問題はない。
第0行は連結標準次数付き商の \(\operatorname{Tor}_0=k\) である。上端では \(b_{q+2}(Q_C)=0\)、\(\binom q{q+1}=0\) を使い、上方では \(S\) の変数数 \(q+2\) の Koszul 複体が消滅する。□

## E-ARTIN　親子計数と、任意体で有効な小行列

任意体上の標準次数付き Artin 商 \(A=T/I\)、\(I_1=0\) に対し、\(h_n=\dim_kA_n\)、\(P=\sum_nh_n\) とする。\(h_0=1,h_1=q\) であり、以下が成り立つ。
\[
 \begin{aligned}
 b_1(A)&\le q+\sum_{n\ge1}\frac{(q-1)h_n}{n+1}\\
 &\le\frac{q-1}{3}P+\frac{(q+1)(q+2)}6,\\
 b_1(A)&\le\frac{q-1}{4}P+\frac{(q+1)^2}{4}
                         +\frac{q-1}{12}h_2,\\
 b_1(A)-P&\le q-1+\sum_{n\ge1}\frac{q-n-2}{n+1}h_n.
 \end{aligned} \tag{E-14}
\]
特に \(q=5\) では \(b_1(A)-P\le14\)。また全 \(i\ge1\) で
\[
 b_i(A)+\binom{q+1}{i+1}\le P\binom qi. \tag{E-15}
\]

証明。斉次初期イデアル \(J\) を取り、次数 \(n\) の標準単項式集合を \(B_n\)、全直接約数が \(B_n\) にある次数 \(n+1\) の単項式集合を \(D_n\) とする。\(J\) の次数 \(n+1\) の極小生成元数は \(\#D_n-h_{n+1}\) である。
子 \(y^\alpha\in D_n\) から親 \(y^{\alpha-e_j}\) への重みを \(\alpha_j/(n+1)\) とする。子ごとの重み総和は1。親 \(y^\gamma\) から候補子への総和は、高々 \(\sum_j(\gamma_j+1)/(n+1)=(n+q)/(n+1)\) である。従って
\(\#D_n\le(n+q)h_n/(n+1)\)。初期イデアルの極小生成元の leading monomial を持つ斉次 Gröbner 基底は \(I\) を生成するので、\(b_1(A)\le\mu(J)\)。\(J_1=0\) を用いて \(n\ge1\) を足すと
\[
 \begin{aligned}
 b_1(A)&\le\sum_{n\ge1}\left(h_n+\frac{q-1}{n+1}h_n-h_{n+1}\right)\\
 &=q+\sum_{n\ge1}\frac{q-1}{n+1}h_n.
 \end{aligned}
\]
この重みは有理数による有限集合の計数であって、係数体の中の除法ではない。
\(n\ge2\) で \(1/(n+1)\le1/3\) とすれば第2式、\(n\ge3\) で \(1/(n+1)\le1/4\) として \(h_2\) を保持すれば第3式を得る。\(P=1+\sum_{n\ge1}h_n\) を引けば最後の式となる。\(q=5\) では \(n\ge3\) の係数は非正なので捨て、\(h_1=5,h_2\le\binom62=15\) を使うと \(4+5+15/3=14\)。ここでは符号付き差を整数または有理数として扱い、負係数を自然数飽和減算で消してはいない。

高次行については Koszul 微分の係数次数0から1への部分を見る。各 \(i\) 元集合 \(J_0\) の列に、行 \((y_{\min J_0},J_0\setminus\{\min J_0\})\) を選ぶ。この行が別の列に現れることはなく、\(A_1\) の変数像は独立なので、選んだ部分行列は符号付き単位行列である。従って任意体で \(\operatorname{rank}d_i\ge\binom qi\)。隣接微分にも同じ議論を適用して
\[
 b_i(A)=P\binom qi-\operatorname{rank}d_i-\operatorname{rank}d_{i+1}
 \le P\binom qi-\binom qi-\binom q{i+1}
\]
を得る。これが (E-15) であり、\(i>q\) では双方0である。小行列の行列式は整数の \(\pm1\) なので、標数2を含む任意体で根拠が保たれる。異なる標数間の rank の一致は用いない。□

## E-GEN　一般 \(q\) の共通出口

(E-TOR) と (E-14)–(E-15) より、固定した同じ \(Q_C\) と \(\widehat R\) に対し
\[
 \boxed{\begin{aligned}
 \beta_1(G)&\le P_C+
 \left\lfloor q+\sum_{n\ge1}\frac{(q-1)h_n}{n+1}\right\rfloor+\widehat R,\\
 \beta_i(G)+\binom{q+1}{i+1}
 &\le P_C\binom{q+1}i+\widehat R\binom{q+1}{i-1}
 \qquad(i\ge1).
 \end{aligned}} \tag{E-GEN}
\]
第一行の harmonic 上界は非負であり、左辺が整数なので床を取れる。必要なら (E-14) の third・fourth・\(q=5\) の差14を代入する。第二式の加法形は自然数の飽和減算を避け、上端もそのまま扱える。減算形を使う場合は右辺から引く二項係数が右辺以下であることがこの加法形から従う。
\(\beta_0=1\)、\(\beta_{q+2}\le\widehat R\)、\(\beta_i=0\) for \(i>q+2\) も含めて全行を覆う。

## E-TWO　二内部変数の四行

\(q=2\)、\(a_1=a<a_2=b\)、\(T=k[y,z]\) とする。\(Q_C\) は単項式 Artin 商であり、\(\sigma_C=\dim_k(0:_{Q_C}(y,z))\) とすれば
\[
 (b_0(Q_C),b_1(Q_C),b_2(Q_C))=(1,\sigma_C+1,\sigma_C).
 \tag{E-16}
\]
従って
\[
 \boxed{\begin{aligned}
 \beta_1(G)&\le P_C+\sigma_C+1+R,&
 \beta_2(G)&\le2P_C+\sigma_C+3R,\\
 \beta_3(G)&\le P_C+3R,&\beta_4(G)&\le R.
 \end{aligned}} \tag{E-TWO}
\]
すべての \(R\) を \(\widehat R\) に換えてもよい。

証明。固定次数 \(n\) の純内部語 \(y^{n-j}z^j\) は offset \(na+j(b-a)\) を持ち、互いに異なる。従って生存する語同士に線形関係はなく、\(T\to Q_C\) の核は単項式で張られる。基底点 \((r,L,K)\) に offset \(a_j\) を掛け、\(r+a_j=s+cu\) と書けば移動先は
\[
 (s,L+1+\epsilon_r-c-\epsilon_s,K+c). \tag{E-17}
\]
これが \(M_s\) の極小点ならその基底元、そうでなければ0となる。各固定乗法の非零像は次数・offset から相異なるので、socle は \(y,z\) の両方で0になる基底点で数えられる。
二変数 Koszul 複体の第0 homology は \(k\)、第2はこの socle である。有限長 \(T\)-加群の分数体上の Euler 等式 \(b_0-b_1+b_2=0\) が (E-16) を与える。これを (E-TOR) に代入すれば (E-TWO) を得る。\(\beta_0=1\)、\(i>4\) の消滅は既述の通りである。□

本章は target への支払いを一切仮定していない。幅別章が行う仕事は、ここで固定した core の \(P_C,W,H_x,\sigma_C\) を評価し、実際の区間補完の容量と比較することだけである。
