# 実 source の kernel–Tor を保つ一般端点定理

この文書は、固定 R38 の `lanes/core/R38_EIGHT_INTERIOR_CORE_PROOF.md` §§2–6 の変数数に依存しない証明を、一般の内部変数数 q で再構成したものである。旧 R39 の原文との byte 一致は主張しない。

## 1. 対象と完備化容量

任意の体 k 上で、真正な最小生成系を

\[
\Gamma=\langle m,m+da_1,\ldots,m+da_q,m+du\rangle,
\quad 0<a_1<\cdots<a_q<u<m,
\quad \gcd(m,d)=\gcd(u,a_1,\ldots,a_q)=1
\]

と書く。e=q+2 とし、その接錐を G とする。比較先は区間完備化
\(\widetilde\Gamma=\langle m,m+1,\ldots,m+du\rangle\) の接錐であり、各 Betti 数は各々の最小生成系に対応する多項式環上で取る。

完備化の実効幅は \(V=\min(du,m-1)\ge u\)。固定入力で採用された算術列接錐の公式は

\[
F_i(v,c)=i\binom v{i+1}+
\begin{cases}(c+1-i)\binom v{i-1}&i\le c,\\
(i-c)\binom vi&i>c,\end{cases}
\qquad 1\le c\le v.
\]

その最小値は

\[
F_i^{\min}(v)=i\binom v{i+1}
 +\min\!\left\{\binom v{i-1},\binom vi\right\}.
\tag{1.1}
\]

各項は v について非減少である。従って実 source の上界を \(F_i^{\min}(u)\) 以下と示せば十分である。範囲外の二項係数は 0 とする。算術列公式自体は固定 R38/R37 の標準依存であり、この計算証明が新たに証明した公式とは扱わない。

なおこの m>u 領域では最小生成性は自動的でもある。もし生成元 \(m+da\) が長さ \(l\ge2\)、offset 和 B の語なら、\((l-1)m=d(a-B)\)。互いに素性から \(l-1=jd,a-B=jm\) で j>=1 となり、a<=u<m に矛盾する。

## 2. 整数コアと有限 Artin 基底

\[
C_{\mathbb Z}=\mathbb Z[s^u,s^{u-a_1}t^{a_1},\ldots,s^{u-a_q}t^{a_q},t^u],
\quad x=s^u,\quad v=t^u,\quad Q_{\mathbb Z}=C_{\mathbb Z}/(x,v).
\]

各単項式は次数・offset 対 (n,b) で区別される。\(S_n\) を
\(\{0,a_1,\ldots,a_q,u\}\) の n 重和集合とすると、Q の次数 n の整数基底は

\[
S_n\setminus\bigl(S_{n-1}\cup(S_{n-1}+u)\bigr).
\tag{2.1}
\]

この基底上の乗法は 0 または別の基底元であり、任意体へ係数を移せる。長さ u の内部語の u+1 個の prefix offset の二つは mod u で一致する。その間の長さ l の非空語は offset ku を持ち、内部 offset は 0 と u の間なので 1<=k<=l-1。この語は \(x^{l-k}v^k\) に等しいため、Q で消える。従って \(Q_n=0\) for n>=u は理論上の停止条件である。

独立再構成には b=r+uK、\(\epsilon_r=[r>0]\)、n=L+K+epsilon_r を使う。各剰余のコアは \(E=\mathbb Z[x,v]\) 上の単項式イデアル M_r を与える。M_r の極小点 (L,K) が Q の基底である。内部 offset a の乗法は、r+a=s+cu に対して

\[
(r,L,K)\mapsto(s,L+1+\epsilon_r-c-\epsilon_s,K+c).
\tag{2.2}
\]

剰余0の (0,0) から実際の語で極小点を作り、支配点を除く。最後に全極小点の全内部乗法が、その上方閉集合へ入ることを、次数制限なしで検査する。生成された点が実際の語であることとこの閉性が、基底の完全性を独立に証明する。

## 3. 実 kernel による補償

コアの (n,b) を指数 nm+db の次数 n 初期形に送ると、同じ実 source への全射 C->G を得る。内部環 T=k[y_1,...,y_q] とし、

\[
Q_G=G/(x,v)G,\quad P_C=\dim_k Q,\quad P=\dim_k Q_G,
\quad R=\dim_k(0:_G(x,v)).
\]

実全射 Q->Q_G の核 K の長さは P_C-P。有限長 T 加群 K の Koszul 鎖群の次元と Tor 長完全列から

\[
b_i(Q_G)\le b_i(Q)+(P_C-P)\binom q{i-1}.
\tag{3.1}
\]

また \(y_j^u=x^{u-a_j}v^{a_j}\) なので G は k[x,v] 上有限である。\(v^m\) と \(x^{m+du}\) は同じ数値指数を持ち、後者がより長いため \(v^m=0\) in G。従って G の k[x,v]-rank は 0。端点 Koszul homology の長さは順に P,P+R,R である。端点と内部変数の Koszul 二重複体より

\[
\begin{aligned}
\beta_i(G)&\le b_i(Q_G)+(P+R)\binom q{i-1}+R\binom q{i-2}\\
&\le b_i(Q)+P_C\binom q{i-1}+R\binom{q+1}{i-1}.
\end{aligned}
\tag{3.2}
\]

これが使用する移行式である。商の Betti 単調性や G の Cohen–Macaulay 性は仮定しない。

## 4. m,d に一様な実 socle 上界

内部 offset の mod u 最短語長を l_r、l_0=0 とし、

\[
W=1+\sum_r l_r,\qquad
H_x=\max\{L:(L,K)\text{ is a minimal point of some }M_r\}.
\]

剰余 r!=0 の最短点 (L_r,K_r) は L_r+K_r=l_r-1。平面単項式イデアルの極小点を第一座標順に並べると、この点の左側に高々 L_r 個、右側に高々 K_r 個ある。M_0=E も加えて

\[
P_C\le W.
\tag{4.1}
\]

より長い実 source 表現との競合は \((n,b)\mapsto(n+jd,b-jm)\), j>=1 に尽きる。長い側の剰余 r のコア点 (L,K) に対し r+jm=s+cu と書くと、競合イデアル T_s は

\[
\bigl(\max(0,L-jd-c+\epsilon_r-\epsilon_s),K+c\bigr)
\tag{4.2}
\]

で生成される。実剰余成分は M_s/(M_s intersect T_s) として E/T_s に入る。したがって両端点 socle は E/T_s の有限 corner に含まれる。

T_s の極小点が z_s+1 個、最後の第二座標が kappa_s なら、任意の (p,q) in T_s について z_s<=p+q-kappa_s。この点を割る極小点の左右の個数を、それぞれ座標減少幅で数えればよい。各最短点に (4.2) の j=1 を適用する。r->(r+m) mod u は置換であり、carry の総和は m。一方 kappa_s>=ceil((m-s)/u) で、その和も m。第一座標は L_r 以下だから

\[
R\le\sum_s z_s\le\sum_r(L_r+K_r)=W-u.
\tag{4.3}
\]

さらに c-epsilon_r+epsilon_s>=floor(jm/u) なので (4.2) の第一座標は max(H_x-jd-floor(jm/u),0)<=max(H_x-2,0)。T_s は純粋な v 冪を含み、極小点の第一座標は相異なる非負整数なので、各 corner 数は max(H_x-2,0) 以下。従って

\[
\boxed{R\le\widehat R=\min\{W-u,u\max(H_x-2,0)\}.}
\tag{4.4}
\]

gcd(m,u)=1、du<m、m,d の有限上限は不要である。P_C+R<=W という誤った代用式は使わない。

## 5. Artin 上界と全体の screen

h_n=dim Q_n、h_1=q とする。標準単項式 y^alpha から y^(alpha+e_j) への重み (alpha_j+1)/(n+1) を数えると、各子への総重みは1、各親からの総重みは (n+q)/(n+1)。初期単項式イデアルへの退化も用い、任意体で

\[
b_1(Q)\le q+\sum_{n\ge1}\frac{(q-1)h_n}{n+1}
\le\frac{q-1}{3}P_C+\frac{(q+1)(q+2)}6.
\tag{5.1}
\]

有理重みは整数の個数を評価するためのもので、基礎体内の除法ではない。後半は h_1=q と、n>=2 で 1/(n+1)<=1/3 による。

Koszul 微分の次数0から次数1への部分で、各 i 元集合 J に対し行 (y_min J,J\{min J}) を選ぶと、元の整数行列上に単位小行列がある。隣接する二つの微分のこの rank 下界を引くと

\[
b_i(Q)\le P_C\binom qi-\binom{q+1}{i+1}.
\tag{5.2}
\]

範囲外の b_i は0であり、(3.2) に代入して

\[
U_1=P_C+\left\lfloor q+\sum_{n\ge1}\frac{(q-1)h_n}{n+1}\right\rfloor+\widehat R,
\]

\[
U_i=P_C\binom{q+1}i+\widehat R\binom{q+1}{i-1}-\binom{q+1}{i+1}
\quad(2\le i\le e).
\tag{5.3}
\]

この screen で不足する候補だけ、Q の正確な有限 Koszul 行列に進む。任意の境界に元の整数行列の determinant +/-1 の r 次小行列があれば、その rank は全体で r 以上。その下界だけでも各 homology は鎖群次元から両隣の r を引いた値以下であり、(3.2) への代入に十分である。

## 6. 反射と最小幅

A を {u-a:a in A} に反射すると、コアの基底は (n,b)->(n,nu-b) で移り、内部変数の置換で Q の Koszul homology も一致する。ただし実 source の H_x、R_hat は向きに依存する。証明書では Q の計算だけを共有し、P_C,W,H_x,R_hat と支払い式は全ての元の向きで計算し直す。

最小幅 u=q+1=e-1 は完全な算術列 source である。算術列公式を全 c で最大化すると、その全行は i*C(e,i+1) 以下。V>=e なら完備化の最小容量がこれを支払う。V=e-1 の場合は d=1 または m=e。前者は source と完備化が同じで、後者は両者とも最大埋込次元 m の接錐で Betti 数が i*C(m,i+1) に一致する。したがって最小幅は全 m,d、全体で閉じる。
