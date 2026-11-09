## Part II — ordinary 側の共通代数

出典略号：V02＝[統合稿](</workspace/NS-P14-Lean/proof_integrated_v2/NS_P14_INTEGRATED_PROOF_JA.md>)、CORE＝[共通代数の可読性監査](</workspace/NS-P14-Lean/auditability_search/CORE_READABILITY_AUDIT.md>)。
ordinary 紙上置換＝[置換証明](</workspace/NS-P14-Lean/auditability_search/ORDINARY_PAPER_REDUCTION_JA.md>)、REFEREE＝[置換の独立監査](</workspace/NS-P14-Lean/auditability_search/ORDINARY_REDUCTION_REFEREE.md>)、SIDON＝[Apéry–Sidon 独立監査](</workspace/NS-P14-Lean/auditability_search/SIDON_INDEPENDENT_AUDIT.md>)。

この Part は真正な最小生成系 \(\Gamma=\langle m=g_1<\cdots<g_e\rangle\)、\(e\ge3\)、同じ体 \(k\) の actual 接錐 \(G\) を固定する。
\(\delta=m-e\)、\(M=m-1\)、\(\mathcal V=e+\delta/2-3/2\) とする。\(\mathcal V\) は物理幅でも正規化幅でもない。
Part II の座標・塔は幅を仮定しないが、target 比較以降は \(w=g_e-m\ge m-1\) を仮定する。
各 \(b_i^R(Z)=\dim_k\operatorname{Tor}_i^R(Z,k)\)、\(c_j^R(Z)=\sum_{i=0}^j(-1)^{j-i}b_i^R(Z)\) は環付きで読む。
多項式環上の有限生成 rank 0 加群では \(c_j\) は第 \(j+1\) syzygy の分数体上の rank で非負である（`X_BASIC`）。
以下の資源は source・体・一つの cut を固定して同時に得る。後で別の cut の良い上界を混ぜる操作はない。

### II.1 `O_COORD` — numerical Apéry 商と同 jump strata

**主張と役割。** \(\operatorname{ord}(v)\) を最長生成元表示の長さとし、\([v]\in G\) を次数 \(\operatorname{ord}(v)\) の数値座標とする。
この座標補題自体は \(e\ge2\) で成立し、\(e=2\) の `O_SIDON` にも同じ定義を使える。
積は \(\operatorname{ord}(u+v)=\operatorname{ord}(u)+\operatorname{ord}(v)\) のとき \([u+v]\)、それ以外は 0 である。
\(x=[m],\ A=G/xG,\ T=(0:_Gx),\ S_0=k[Y_2,\ldots,Y_e]\) と置く。
\(A\) の非 Apéry head の張る部分 \(N\) は \(S_0\)-斉次イデアルであり、actual 商 \(Q=A/N\) は数値 Apéry 座標を基底とする。
\[
q_s=\dim Q_s,\quad \nu=\max\{s:q_s\ne0\},\quad a=q_2,\qquad
q_0=1,\ q_1=e-1,\ \sum_{s\ge2}q_s=\delta,\ A_2=Q_2,\ \nu\le\delta+1. \tag{O1}
\]
terminal \(\tau\in T\) と非 Apéry head \(\tau+m\in N\) は基底として一対一に対応し、
\(d(\tau)=\operatorname{ord}(\tau+m)-\operatorname{ord}(\tau)\) は \(2\le d(\tau)\le\nu\) を満たす。
**証明の核心。** 前駆元 \(v-m\in\Gamma\) の存在は非 x 生成元による積で保たれるので \(N\) はイデアルである。
生きた \(T\)-作用 \(\tau\mapsto\sigma\) は \(d(\sigma)\ge d(\tau)\)、生きた \(N\)-作用は逆に \(d(\sigma)\le d(\tau)\) を与える。
\[
D_sT=\langle\tau:d(\tau)\ge s\rangle,\quad
F_sN=\langle\tau+m:d(\tau)\le s\rangle,\quad
\operatorname{gr}_s^D T\ \simeq\ F_sN/F_{s-1}N\quad\text{（次数を }s\text{ 上げる）}. \tag{O2}
\]
作用が一致するのはこの**同 jump の stratum のみ**であり、\(T\cong N\) という全体同型は主張しない。
\(I_Q\) は次数 \(\nu+1\) 以下で生成されるので \(N=I_Q/I_A\) の極小 head の次数も高々 \(\nu+1\)；terminal の次数は少なくとも 1、以後の head 作用では jump が増えないため上界が伝播する。
**完全証明・次への接続。** V02 §2 と CORE 監査「§2・§5」。これが塔の実在と `O_SIDON` の actual 性を保証する。

### II.2 `O_VOLUME` — 最短 offset 経路による有限総資源

**主張。** 剰余 \(\rho\) に対し、正 offset \(g_i-m\ (i>1)\) の和の最小値を \(b_\rho\)、その値を実現する最短語長を \(l_\rho\) とする。
Apéry 元 \(\omega_\rho\) について \(s_\rho=\operatorname{ord}(\omega_\rho),\ L_\rho=(\omega_\rho-b_\rho)/m\) と置く。
非零剰余を \(b_\rho\) の昇順で \(\rho_k\) と並べると
\[
1\le s_\rho\le L_\rho\le l_\rho,\qquad
L_{\rho_k}-1\le\min(\delta,k-1),\qquad
\sum_{\rho\ne0}(L_\rho-1)\le\delta\mathcal V. \tag{O3}
\]
さらに \(v_\rho(q)=\operatorname{ord}(\omega_\rho+qm)\) は \(q\ge l_\rho-L_\rho\) で \(L_\rho+q\) に安定し、
\[
\sum_{\tau\equiv\rho\ (m)}(d(\tau)-1)=L_\rho-s_\rho. \tag{O4}
\]
**証明の核心。** least-offset 語の prefix も least-offset で、正の cycle を除けるため prefix 剰余は相異なる。
\(e-1\) 個の atom 剰余では \(L\) は増えず、残る \(\delta\) 個の非 atom 剰余でだけ高々 1 増える。
従って \(L_{\rho_k}-1\le\min(\delta,k-1)\)；和は \(\delta(e+\delta/2-3/2)\) となる。
安定化までの order 増分の余剰を足すと (O4) を得る。
**完全証明・接続。** V02 §3, (3.1)–(3.3)。数値半群内部の議論だけで `O_TOWER` の有限性と同一総量を与える。

### II.3 `O_CUT` — 同標数で一つの square-zero cut を固定

**主張。** \(p(a)=\max\{p\ge0:\binom{p+1}{2}\le a\},\ r=\max(2,p(a))\) とすると \(2\le r\le e-1\) であり、
必要なら `I_FIELD` の同標数の純超越拡大後、独立な非 x 一次形式 \(E=(\lambda_1,\ldots,\lambda_r)\) を一度選んで
\[
(A/EA)_{\ge2}=0,\qquad P=k[\lambda_1,\ldots,\lambda_r] \tag{O5}
\]
とできる。以後この \(P\) を変えない。
**証明の核心。** \(a=\binom{p+1}{2}+b,\ 0\le b\le p\) に対し `X_GREEN` を反復すると、\(s\le p\) 本の一般形式で切った二次元は
\(\binom{p+1-s}{2}+\max(b-s,0)\) 以下；\(s=p\) で 0。\(p<2\) なら 2 本に拡張する。
標準生成により高次も消える。有限体の場合も intrinsic Betti 数は同標数の体拡大で保存される。
**完全証明・接続。** V02 §4。`O_COORD` の \(S_0\)-完全列・strata はこの \(P\) へ制限でき、次の塔に用いる。

### II.4 `O_TOWER` — actual 完全列と唯一の資源列

**主張。** \(F_s=F_sN\)、\(F_1=0\)、\(F_\nu=N\) とし、\(2\le s\le\nu\) に対して
\[
U_s=A/F_{s-1},\ X_s=(U_s)_{\ge s},\ M_s=(U_s)_{\ge s+1},\ K_s=F_s/F_{s-1},
\quad0\to K_s\to M_s\to X_{s+1}\to0,\quad X_{\nu+1}=0. \tag{O6}
\]
\(U_s\) は次数 \(s\) まで \(Q\) と一致する。cut により \(X_s,M_s\) はそれぞれ単一次数 \(s,s+1\) で生成され、
\(\mu_P(X_s)=q_s,\ \mu_P(M_s)=h_{s,1}\) である。
\[
h_{s,t}=\dim(X_s)_{s+t},\quad H_t=\sum_{s=2}^{\nu}h_{s,t},\quad S=\sum_{t\ge0}H_t,
\quad H_0=\delta,\quad0\le H_t\le M,\quad S=\sum_{\rho\ne0}(L_\rho-1)\le\delta\mathcal V. \tag{O7}
\]
次数 1 の terminal 数を \(\ell\) とすると、同じ列について同時に
\[
H_1=\delta-a+\ell\le M-a,\qquad H_1\le r\delta;\qquad
r\ge3\Longrightarrow a\ge a_r:=\binom{r+1}{2},\quad H_1\le M-a_r. \tag{O8}
\]
\(\delta=0\) なら \(\nu=1,N=T=X_2=0\) で空塔・零資源列と読む。
**証明の核心。** jump \(s\) の head の次数は少なくとも \(s+1\) なので \(K_s\subset M_s\)、かつ
\(M_s/K_s=(U_{s+1})_{\ge s+1}=X_{s+1}\) である。
剰余 \(\rho\) の Apéry 座標は \(t\in[0,s_\rho-2]\)、次数 \(p\)、jump \(d\) の terminal head は \(t\in[p,p+d-2]\) に寄与する。
同じ剰余の次の terminal 次数は少なくとも \(p+d\) なので区間は互いに素；各剰余は各 \(t\) に高々 1 を寄与する。
長さの和は \((s_\rho-1)+\sum(d-1)=L_\rho-1\)。また \(H_1\le\sum_s r q_s=r\delta\)。
**完全証明・接続。** V02 §5 と CORE 監査「区間計数」。この一列を `O_TOR` 以後の全 rank、全 scalar 評価に使う。

### II.5 `O_HARMONIC` — 同一次数生成加群の Koszul rank 評価

**主張。** 任意体上の \(r\) 変数多項式環 \(P\) と、次数 \(b\) だけで極小生成される有限長加群 \(Z\) に対し、
\(h_t=\dim Z_{b+t}\) とすれば
\[
c_j^P(Z)\le\binom{r-1}{j}\sum_{t\ge0}\frac{j}{t+j}h_t\quad(1\le j<r),\qquad
c_0^P(Z)=\mu_P(Z),\quad c_r^P(Z)=0. \tag{O9}
\]
**証明の核心。** 同 shift の表示 \(P^q\twoheadrightarrow Z\) の初項加群商 \(Z^*\) に対し、ラベル順の Koszul 境界は block 三角形で
\(R_i(Z)\ge R_i(Z^*)\) となる。単項式商では \(v\notin F\) の target \((m,F)\) に source \((m/x_v,F\cup\{v\})\) を対応させ、対角 \(\pm1\) 小行列を得る。
多重次数 \(\alpha\) ごとに重み \(\alpha_v/(t+j)\) で整数 rank を平均すると
\[
R_{j+1}\ge\binom{r-1}{j}\sum_{t\ge0}\frac{t}{t+j}h_t,\qquad
c_j=\binom{r-1}{j}\operatorname{length}Z-R_{j+1}.
\]
分母を体で割る議論ではなく有理数による rank の数値評価なので、正標数にもそのまま成立する。
**完全証明・接続。** V02 §6, (6.1), (H) と CORE 監査「§6」。`O_TOWER` の単一次数生成性に適用する。

### II.6 `O_TOR` — strata から相対 Tor へ進む三段の鎖

**主張。** \(R=k[x,E]\) とし、この節の \(c_j(G)\) は \(c_j^R(G)\) を表す。
任意の完全列 \(0\to K\to M\to L\to0\) について connecting rank を \(d_i\) とすると
\[
c_j(M)=c_j(K)+c_j(L)-d_{j+1},\quad
c_j(K)=c_j(M)+c_{j+1}(L)-[b_{j+1}(L)-d_{j+1}]. \tag{O10}
\]
減算する \(d_{j+1}\) とその補数はともに非負（後者は Tor の像の次元）である。
\(x\)-Koszul homology の 0,1 行に対する唯一の後続微分を
\(\rho_i=\operatorname{rank}(d_2:\operatorname{Tor}_i^P(A,k)\to\operatorname{Tor}_{i-2}^P(T,k))\) とすると
\[
b_i^R(G)=b_i^P(A)+b_{i-1}^P(T)-\rho_i-\rho_{i+1},\quad
c_j(G)=c_j^P(A)+c_{j-1}^P(T)-\rho_{j+1}. \tag{O11}
\]
内部次数 shift は total 次元に影響しない。\(d_2=0\) は仮定しない。
\(B=A/X_2\cong P/P_+^2\oplus k(-1)^{e-r-1}\)、\(L_j=c_j^P(B)=(e-1)\binom{r-1}{j}-\binom{r-1}{j+1}\) と置く。
各 \(1\le j\le r\) について必要な鎖を省略せずに書く：
\[
\begin{aligned}
c_j(G)&\le L_j+c_j^P(X_2)+c_{j-1}^P(T),\\
c_{j-1}^P(T)&\le\sum_{s=2}^{\nu}c_{j-1}^P(K_s),\\
c_{j-1}^P(K_s)&\le c_{j-1}^P(M_s)+c_j^P(X_{s+1}).
\end{aligned} \tag{O12}
\]
第 2 行だけが同 jump strata を用い、第 3 行は (O6),(O10) を用いる。
\(X_{\nu+1}=0\) により \(X_s\) の項が一巡し、\(j=1\) では \(c_0(M_s)=\mu_P(M_s)\) を正確に保つ。
**結論。** (O9) より \(c_j(G)\le L_j+\sum_{t\ge0}W_j(t)H_t\)、ただし
\[
\begin{gathered}
W_1(0)=r-1,\quad W_1(1)=(r+1)/2,\quad W_1(t)=(r-1)/(t+1)\ (t\ge2),\\
W_j(0)=\binom{r-1}{j},\quad
W_j(t)=\frac{j\binom{r-1}{j}}{t+j}+\frac{(j-1)\binom{r-1}{j-1}}{t+j-2}\quad(2\le j\le r,\ t\ge1).
\end{gathered} \tag{O13}
\]
**完全証明・接続。** V02 §7, (7.1)–(7.3)；CORE 監査「§7」の三段鎖と補正。これを actual target の容量と比較する。

### II.7 `O_TARGET` — 第 0 homology の補正と actual target の係数

**仮定・主張。** \(w\ge m-1\) とする。`I_TARGET` の actual completion に対し
\(T_m(z)=1+\sum_{i\ge1}i\binom m{i+1}z^i\) である。
\(E\) を非 x 一次空間の基底に拡張し、残りを \(Z\)、\(f=e-r-1\)、\(C(z)=\sum_{j=1}^rc_j(G)z^j\) とする。
相対 Betti 多項式と第 0 homology は正確に
\[
\mathcal B_G^R=(1+z)((f+1)+C(z)),\qquad H_0(K_R(G))\cong k[Z]/(Z)^2.
\]
二重複体の 0 行だけをその正確な Betti 多項式 \(T_{f+1}\) で、高次行を \(Z\)-Koszul 鎖群で抑えると
\[
\begin{aligned}
\mathcal B_G&\preceq T_{f+1}+(1+z)^f[\mathcal B_G^R-(f+1)]\\
&=T_{f+2}+(1+z)^{f+1}C(z)
=T_{e-r+1}+(1+z)^{e-r}C(z).
\end{aligned} \tag{O14}
\]
ここで引く定数 \(f+1\) が第 0 homology の補正であり、\(T_{f+2}-T_{f+1}=(f+1)z(1+z)^f\) を使った。
後続微分は total homology 次元を減らすので、退化や商の Betti 単調性を要しない。
\(q=e-r,\ N_*=\delta+r-1=m-q-1\) と置くと exact な target 差は
\[
\begin{aligned}
T_m-T_{q+1}
&=(1+z)^q\sum_{a=0}^{N_*-1}(q+1+a)z(1+z)^a\\
&=(1+z)^q\sum_{j=1}^{N_*}R_jz^j,\qquad
R_j=(q+j)\binom{N_*}{j}+j\binom{N_*}{j+1}. \tag{O15}
\end{aligned}
\]
係数恒等式は \(\sum_{a=0}^{N_*-1}(q+1+a)\binom a{j-1}=R_j\)；hockey-stick と
\(a\binom a{j-1}=(j-1)\binom a{j-1}+j\binom aj\) による。
従って \(c_j(G)\le R_j\ (1\le j\le r)\) は**全 Betti 行**の十分条件であり、\(j>r\) の余る係数は非負である。
さらに Vandermonde 展開により
\[
\begin{aligned}
R_j-L_j&=\mathcal V[\binom{\delta+r-1}{j}-\binom{r-1}{j}]+\Gamma_j,\\
\Gamma_j&=\delta\binom{r-1}{j-1}
+\tfrac12\sum_{u=2}^j[3\binom{r-1}{j-u}+(u-2)\binom r{j-u+1}]\binom\delta u
+\tfrac{j-1}{2}\binom\delta{j+1},\\
R_j-L_j&\ge\delta(\mathcal V+1)\binom{r-1}{j-1}\quad(1\le j\le r). \tag{O16}
\end{aligned}
\]
最後は \(\binom{\delta+r-1}{j}-\binom{r-1}{j}=\sum_{v=1}^{\delta}\binom{r-2+v}{j-1}\ge\delta\binom{r-1}{j-1}\) と各項の非負性による。
\(\delta=0,N_*=r-1\) でも範囲外二項係数を 0 とすれば \(R_r=0\) を含め有効。
**完全証明・接続。** V02 §8, (8.1)–(8.4)；CORE 監査 (A8.1),(A8.2)。Part III はこの十分条件を全ての actual cut について満たす。

## Part III — ordinary 側の全域閉鎖

### III.1 `O_LOW` — \(r=2,3\) の直接評価

**主張。** 任意の ordinary source の actual cut が \(r=2\) または 3 なら全 \(c_j(G)\le R_j\) が成立する。
\(r=2\) では同じ列の \(H_1\le S-\delta\) と \(H_1\le2\delta\) を使い
\[
c_1-L_1\le\min\{\tfrac32S-\tfrac12\delta,\ \tfrac52\delta+\tfrac12S\}
\le\delta(\mathcal V+1),\qquad c_2\le S-\delta.
\]
前者の二評価はそれぞれ \(\mathcal V\le3\)、\(\mathcal V\ge3\) で払う。\(\delta=0\) の空塔も含む。
\(r=3\) なら \(e\ge4,a\ge6,\delta\ge6,\mathcal V\ge11/2\) で、
\[
c_1-L_1\le\tfrac43\delta+\tfrac43H_1+\tfrac23S,\qquad
c_2-L_2\le3\delta+\tfrac32S,\qquad c_3\le S-\delta.
\]
第 1 rank には \(H_1\le M-6\) を使う。\(z=\delta-6\) に対して
\(\delta(\mathcal V-1)-4(M-6)=(z+2)e+\binom z2+7>0\) なので必要な余裕は正。
第 2 rank は \(W_2(0)=1,W_2(1)=8/3,W_2(t)\le3/2\ (t\ge2)\) と \(H_1\le3\delta\) により得られ、
\(2\delta(\mathcal V+1)-(3\delta+\tfrac32\delta\mathcal V)=\delta(\mathcal V/2-1)\ge0\)。top rank も (O16) で払える。
**完全証明・接続。** V02 §9；CORE 監査「§9」。残る \(r\ge4\) だけを scalar 化する。

### III.2 `O_SCALAR` — 全 rank から一つの数への還元

**主張。** \(r\ge4\) とし、同じ \(H_t\) について
\[
F_r=(r-1)\delta+\tfrac{r+1}{2}H_1+\sum_{t\ge2}\tfrac{r-1}{t+1}H_t,\qquad
c_j(G)\le L_j+\binom{r-1}{j-1}F_r\quad(1\le j\le r). \tag{O17}
\]
**証明の核心。** \(j\ge2,t\ge1\) の正規化重みは \((r-j)/(t+j)+(j-1)/(t+j-2)\)。
\(j\ge3\) では各分母を \(t+1\) と比較する。\(j=2\) と基準重みとの差は
\([2-(r-3)t]/[t(t+1)(t+2)]\) で \(t\ge2\) なら非正。
例外 \(j=2,t=1\) も \((r+1)/3\le(r+1)/2\)；\(t=0\) は \((r-j)/j\le r-1\)。top rank まで含む。
**完全証明・接続。** V02 §10, (10.1),(10.2)。`O_TARGET` より \(F_r\le\delta(\mathcal V+1)\) だけを以後証明すればよい。

### III.3 `O_SIDON` — actual 最大二次層と実現不可能な角

**主張。** 真正な最小生成系の actual 数値 Apéry 商 \(Q\) では、任意体・\(e\ge2\) に対し
\[
q_2=\binom e2\ \Longrightarrow\ m\ge e(e-1)+1\ \Longrightarrow\ \delta\ge(e-1)^2. \tag{O18}
\]
**証明の核心。** 二次単項式から \(Q_2\) への全射が同型なので、すべての二次積は相異なる次数 2 の Apéry 座標である。
\(B=\{0,\overline g_2,\ldots,\overline g_e\}\subset\mathbb Z/m\mathbb Z\) の反復を許す unordered 二項和はすべて異なる。
二次積と 0・atom の剰余の一致も、同じ剰余の Apéry 元の一意性と次数 0,1,2 の違いから排除される。
\(b-c=b'-c'\) なら \(b+c'=b'+c\)；二項和の一意性により、\(b\ne c\) の順序対の差は非零剰余へ単射。
よって \(e(e-1)\le m-1\)。合成数・偶数 \(m\)、標数 2 も例外ではない。
**actual cut への適用条件。** \(r=e-1\) **かつ \(r\ge3\)** のときだけ \(r=p(q_2)\) より \(q_2\ge a_r=\binom e2\) と結論する。
従って \(e=r+1,\delta=a_r\) は \(\delta\ge r^2>a_r\) に反し、特に \(r=6,7,8\) の三つの角は存在しない。
\(r=2\) にはこの cut の含意を適用しない：\(\langle6,7,11\rangle\) は \(r=e-1=2,\delta=3=a_2,q_2=2\) である。
**完全証明・接続。** ordinary 紙上置換 §1 (SO1),(SO2)；SIDON 独立監査 §§1–4。抽象 Hilbert profile への主張ではなく、次の負の基点だけを actual 性で除く。

### III.4 `O_SMALL` — \(4\le r\le8\) の固定 cutoff 恒等式と五行表

**仮定。** actual cut の \(r\in\{4,5,6,7,8\}\)、整数 \(e\ge r+1,\delta\ge a=a_r\)、同じ資源列 (O7),(O8)。
整数 \(n\ge r\) を固定し、\(\alpha=(r-1)/(n+1),\ c=(r+1)/2-\alpha,\ \mathcal H_n=\sum_{j=1}^n1/j\) とする。
\[
F_r\le U(e,\delta):=\alpha\delta\mathcal V+(r-1-\alpha)\delta+c(M-a)
+M\sum_{j=2}^{n-1}\left(\frac{r-1}{j+1}-\alpha\right). \tag{O19}
\]
各重みから \(\alpha\) を引くと \(j<n\) の残余係数は正、\(j=n\) は 0、\(j>n\) は負なので、台を切り捨てる仮定なしにこの上界を得る。
\(G(e,\delta)=\delta(\mathcal V+1)-U(e,\delta)\)、\(e=r+1+s,\delta=a+t\)、**整数** \(s,t\ge0\) と書く。
\[
\begin{gathered}
g=G(r+1,a),\quad A=a-1-(r-1)\left(\mathcal H_n-2+\frac{a+2}{n+1}\right),
\quad b=G(r+1,a+1)-G(r+1,a)=A+2-\alpha(r-1),\\
\boxed{G(r+1+s,a+t)=g+sA+tb+(1-\alpha)\left(\binom t2+st\right).} \tag{O20}
\end{gathered}
\]
これは \(A(a+t)=A+(1-\alpha)t\) と \(G(r+1,a+t+1)-G(r+1,a+t)=b+(1-\alpha)t\) を足す exact な恒等式である。

| \(r\) | \(a\) | \(n\) | 正分母 \(L\) | \(Lg\) | \(LA\) | \(Lb\) |
|---:|---:|---:|---:|---:|---:|---:|
|4|10|7|280|2443|762|1007|
|5|15|10|6930|39380|28429|32209|
|6|21|13|72072|−7479|424147|439591|
|7|28|17|2042040|−12196485|17076937|17076937|
|8|36|21|739024|−5070732|8418651|8250691|

全行で \(A,b,1-\alpha>0\)。\(r=4,5\) は \(g>0\)。\(r=6,7,8\) は \(g+A>0,g+b>0\) なので \(s+t\ge1\) なら正である。
\(\binom t2,st\ge0\) は整数性から従い、残る \(s=t=0\) は `O_SIDON` で排除する。
従って全 actual source の \(4\le r\le8\) について \(F_r<\delta(\mathcal V+1)\)。有限点から無限域への外挿ではなく (O20) が全称性を与える。
**完全証明・接続。** ordinary 紙上置換 §§2–3 (SO3)–(SO5)；ORDINARY_REDUCTION_REFEREE の係数・符号監査。
五行は Fraction による厳密算術で補助確認できるが、actual 性・塔・Tor 接続は紙上補題を用いる。

### III.5 `O_LARGE` — \(r\ge9\) のみを残した既存大 rank 評価

**主張と範囲。** actual cut の \(r\ge9\) なら \(e\ge r+1\ge10\)、\(\delta\ge a=r(r+1)/2\) なので既存 V02 §11 の評価で閉じる。
ここで必要な旧 seed は **\(r=9\) の一行のみ**。旧 \(r=4,\ldots,8\) の五行は主依存から外す。
\(D=\lfloor a/2\rfloor+1\)、\(\alpha=(r-1)/(D+1)\) を \(\delta\) によらず固定し、(O19) の \(n=D\) による上界を \(U_r\)、差を \(G_r\) とする。
\[
\begin{gathered}
G_r(e,\delta)=G_r(10,\delta)+(e-10)A_r(\delta),\quad
A_r(\delta)=\delta-1-(r-1)\left(\mathcal H_D-2+\frac{\delta+2}{D+1}\right),\\
g_0=G_r(10,a)=(r-1)(a+9)(T_r-\mathcal H_D),\\
T_r=\frac{a(a+22-r)}{2(r-1)(a+9)}+\frac{2r-3}{r-1}
-\frac{a(a+21)+36}{2(D+1)(a+9)}. \tag{O21}
\end{gathered}
\]
\(r=9\) では \(a=45,D=23,T_9=269/72\)、\(T_9-747/200=1/900>0\)、\(\mathcal H_{23}=444316699/118982864<747/200\) なので \(g_0>0\)。
\(r\ge10\) では \(B(r)=r/4+1+9/(2r)\)、\(T_1(r)\) を (O21) の最後の分母 \(2(D+1)(a+9)\) を \((a+3)(a+9)\) に替えた値とする。
\[
T_1(r)-B(r)=\frac{r^3[(r-10)(2r+15)+2]+r[111(r-10)+210]+972}
{2r(r-1)(r^2+r+6)(r^2+r+18)}>0,
\]
かつ \(T_1(r)\le T_r\) である。
\(\mathcal H_{28}<B(10)\) と、凸性による \(\mathcal H_{D_{r+1}}-\mathcal H_{D_r}<2/r<B(r+1)-B(r)\) を帰納して \(\mathcal H_D<B(r)<T_r\) を得る。
\(A_0=A_r(a)\) とすると、さらに V02 (S21)–(S27) は
\[
g_0=(a+9)A_0+C,\quad C=\frac{a[-a(D-r+2)-D(r-4)+3]}{2(D+1)}<0,
\quad A_0>0,\quad b_0=A_0+11-r-8\alpha>\tfrac14. \tag{O22}
\]
最後の符号判定は \(b_0> a/2-3r/2+11/2+3(5r+31)/(2(a+9))-17(r-1)/(a+3)>9/2-17/4=1/4\) による。
従って整数 \(t=\delta-a\ge0\) について
\[
A_r(a+t)=A_0+(1-\alpha)t>0,\quad
G_r(10,a+t)=g_0+t b_0+(1-\alpha)\binom t2>0,\quad
G_r(e,\delta)>0. \tag{O23}
\]
**完全証明・接続。** V02 §11 (S2)–(S9),(S10) の有理数 bound、旧表の \(r=9\) 行のみ、(S12)–(S31)。
正係数分解・凸性・差分恒等式が無限域を証明し、有限診断はその代わりにしない。`O_SCALAR` と `O_TARGET` に戻して全行を得る。

### III.6 `O_CLOSE` — ordinary 枝の coverage と任意体への帰着

**結論。** 任意体 \(k\)、真正な \(e\ge3\) の数値半群で \(w\ge m-1\) なら、すべての \(i\ge0\) に対し
\(\beta_i(G_\Gamma;k)\le i\binom m{i+1}\)（\(i\ge1\)）、第 0 行は 1 である。
actual cut は必ず \(2\le r\le e-1\)。\(r=2,3\) は `O_LOW`、\(4\le r\le8\) は `O_SMALL`、\(r\ge9\) は `O_LARGE` によって閉じる。
後二者は `O_SCALAR`、全枝は `O_TARGET` を通って actual ordinary completion へ達する。相対 top rank \(j=r\) とそれ以降の Betti 行も (O13)–(O17) に含まれる。
Green に必要な体拡大だけを `I_FIELD` で戻す。異標数間の rank 一致は仮定せず、各体に同じ議論を適用する。
\(e=1,2\) と narrow 側は Part VI の別枝に残し、この命題の範囲と混同しない。
**主依存から除外。** 旧 V02 §15 全体、first-hit、truncated lex、83 profile・665 比較・5 infinite tail、ナヴィ代替増分法はこの DAG に入らない。
旧稿・検算・代替証明は歴史的資料として保存する。新たな数学的欠落はこの担当範囲では発見していない。
**監査状態。** CORE は §§2–10 の接続、REFEREE は置換と既存基礎への接続、SIDON は actual 補題、V02 FINAL/LATER は §11 の代数をそれぞれ確認する。
これらは独立数学監査の記録であり、公刊定理原典の全面再査読・全定理の最終査読・Lean 形式認証ではない。
