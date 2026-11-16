# 2　ordinary target：一つの塔・一つの資源列による全行比較

この章では \(S=\langle m=g_1<\cdots<g_e\rangle\)、\(e\ge3\)、任意体 \(k\) を固定する。
接錐 \(G=\operatorname{gr}_{\mathfrak m}k[[t^S]]\) は元の \(S\) のものを使う。

\[
\delta=m-e,\qquad M=m-1,\qquad \mathcal V=e+\delta/2-3/2.
\]

この \(\mathcal V\) は資源量であり、物理幅・正規化幅ではない。
幅の仮定 \(g_e-m\ge m-1\) は §2.5 の target 比較以降でのみ用いる。
負の下添字または上添字を超える下添字の二項係数は 0 とする。

## 2.1　数値座標、逆向きの jump filtration、有限総量

**補題 O1（actual 座標と同 jump stratum）。**


\(\operatorname{ord}(v)\) を \(v\in S\) の最長原子表示長とする。
各次数の接錐は \(\operatorname{ord}(v)=n\) の初期単項式 \([v]\) を基底とし、

\[
[v][w]=\begin{cases}[v+w],&\operatorname{ord}(v+w)=\operatorname{ord}(v)+\operatorname{ord}(w),\\
0,&\operatorname{ord}(v+w)>\operatorname{ord}(v)+\operatorname{ord}(w).
\end{cases}
\]

\(x=[m]\)、\(A=G/xG\)、\(T=(0:_Gx)\)、\(S_0=k[Y_2,\ldots,Y_e]\) と置く。
\(A\) の基底は生きた \(x\)-矢印が入らない数値座標（head）である。
このうち非 Apéry head の張る部分 \(N\) は \(S_0\)-斉次イデアルであり、\(Q=A/N\) は
\(\operatorname{Ap}(S,m)=\{\omega_\rho:0\le\rho<m\}\) を基底とする標準次数付き Artin 代数である。
\(q_s=\dim_kQ_s\)、\(a=q_2\)、\(\nu=\max\{s:q_s\ne0\}\) とすると

\[
q_0=1,\quad q_1=e-1,\quad \sum_{s\ge2}q_s=\delta,
\quad A_2=Q_2,\quad \nu\le\delta+1. \tag{O1}
\]

\(T\) の基底である terminal \(\tau\) に対し
\(d(\tau)=\operatorname{ord}(\tau+m)-\operatorname{ord}(\tau)\) と置けば、
\(\tau\mapsto\tau+m\) は非 Apéry head への全単射、\(2\le d(\tau)\le\nu\) である。
\[
D_sT=\langle\tau:d(\tau)\ge s\rangle,\qquad
F_sN=\langle\tau+m:d(\tau)\le s\rangle
\]
はそれぞれ降順・昇順の \(S_0\)-filtration であり、同 jump の層だけについて
\[
D_sT/D_{s+1}T\ \simeq\ F_sN/F_{s-1}N \tag{O2}
\]
が成り立つ。右辺の次数は左辺より \(s\) 大きい。

**証明。** \(\mathfrak m^n\) は order \(\ge n\) の単項式を支持に持つ級数からなる。
これは長さ \(n\) の正元分解と原子分解からの両包含で従うので、商
\(\mathfrak m^n/\mathfrak m^{n+1}\) の座標と積は表示のとおりである。
\(v-m\in S\) なら \(v+g_i-m\in S\) だから、生きた非 \(x\) 作用は非 Apéry 性を保ち、\(N\) はイデアルとなる。
Apéry 元の最長表示は \(m\) を含まず、その全 prefix も order を正しく実現する。
従って \(Q\) は上記座標で標準生成され、length は \(m\) である。
次数 1 の Apéry 元は正確に非 \(m\) 原子なので (O1) の計数が従う。
terminal は正で jump は 2 以上、対応 head の次数は 3 以上なので \(A_2=Q_2\) である。
標準生成 Artin 代数では最高次数まで Hilbert 関数が途切れないので \(\nu-1\le\delta\) を得る。

\(\sigma=\tau+g_i\) に対し、\(T\) の作用が生きるなら
\(\operatorname{ord}(\sigma)=\operatorname{ord}(\tau)+1\) と
\(\operatorname{ord}(\sigma+m)\ge\operatorname{ord}(\tau+m)+1\) より \(d(\sigma)\ge d(\tau)\)。
head 側の作用が生きるなら逆に
\(\operatorname{ord}(\sigma+m)=\operatorname{ord}(\tau+m)+1\) と
\(\operatorname{ord}(\sigma)\ge\operatorname{ord}(\tau)+1\) より \(d(\sigma)\le d(\tau)\)。
jump が等しければ一方の生存は他方の生存と同値であり、両作用の係数は同じ 1 である。
これで (O2) を得る。全体の \(T\cong N\) は必要なく、一般にはこの推論から得られない。

最後に \(Q=S_0/I_Q\)、\(A=S_0/I_A\) と書く。
\(Q_{\nu+1}=0\) なので \(I_Q\) は次数 \(\nu+1\) 以下で生成され、\(N=I_Q/I_A\) も同じ上界で生成される。
極小 head の terminal 次数は 1 以上だから、その jump は \(\nu\) 以下。
head 作用で jump が増えないことから、この上界は全 head に伝播する。□

**補題 O2（最短 offset 経路）。**

剰余 \(\rho\pmod m\) に対し、正 offset \(g_i-m\ (i>1)\) の和で \(\rho\) を表す最小値を
\(b_\rho\)、それを実現する最短語長を \(l_\rho\) とする。
\(b_0=l_0=0\)、\(s_\rho=\operatorname{ord}(\omega_\rho)\)、
\(L_\rho=(\omega_\rho-b_\rho)/m\) と置く。非零剰余を \(b_\rho\) の昇順で \(\rho_k\) と並べると

\[
1\le s_\rho\le L_\rho\le l_\rho,\qquad
L_{\rho_k}-1\le\min(\delta,k-1),\qquad
\sum_{\rho\ne0}(L_\rho-1)\le\delta\mathcal V. \tag{O3}
\]

各剰余の terminal は有限個であり、
\[
\sum_{\tau\equiv\rho\ (m)}(d(\tau)-1)=L_\rho-s_\rho. \tag{O4}
\]

**証明。** \(\gcd(m,g_2-m,\ldots,g_e-m)=1\) により offset の剰余は巡回群を生成し、各最小値が存在する。
Apéry 元の最長表示の offset は \(b_\rho\) 以上、最小 offset 語の数値重み
\(b_\rho+ml_\rho\) は \(\omega_\rho\) 以上だから、最初の不等式を得る。

最小 offset 語の prefix も最小 offset である。より小さい offset の prefix に置換すると最小性に反する。
prefix 剰余は相異なる。同じ剰余を二度通るなら、その間の正 offset cycle を除けるからである。
最初の prefix は原子で \(L=1\)。次の原子を加えると Apéry 最小性から \(L\) は高々 1 増す。
到達剰余が原子剰余なら、原子は先行 Apéry 元と次の原子の正の和と等しくなれないから、\(L\) は増えない。
異なる非 \(m\) 原子は異なる非零剰余を持つ。同じ剰余なら、大きい原子が小さい原子と \(m\) の正の倍数に分解されるからである。
従って原子剰余は \(e-1\) 個で、残る非零剰余は \(m-1-(e-1)=\delta\) 個。
従って経路中の増加回数は \(\delta\) 以下であり、\(\rho_k\) に至る prefix は最初の \(k\) 頂点中にあり
そのうち最初の一つは原子なので、\(k-1\) 以下でもある。
これが (O3) の中段で、その和は
\(\sum_{k=1}^{m-1}\min(\delta,k-1)=\delta(e+\delta/2-3/2)\) である。

\(v(q)=\operatorname{ord}(\omega_\rho+qm)\) は \(v(q+1)\ge v(q)+1\) を満たす。
最小 offset 語に \(m\) を加えた表示により、\(q\ge l_\rho-L_\rho\) では
\(v(q)=L_\rho+q\)。より長い表示は \(b_\rho\) より小さい offset を与えるので不可能である。
ゆえに \(x\)-矢印は有限回しか死なず、
\(\sum_{q\ge0}(v(q+1)-v(q)-1)=L_\rho-s_\rho\) を telescoping すれば (O4) となる。□

## 2.2　一つの cut から actual tower と資源列を同時に得る

**補題 O3（固定 cut と資源）。**


\(p(a)=\max\{p\ge0:\binom{p+1}{2}\le a\}\)、\(r=\max(2,p(a))\) と置く。
必要なら \(k\) を同標数の無限純超越拡大へ移す。
独立な非 \(x\) 一次形式 \(E=(\lambda_1,\ldots,\lambda_r)\) を一度選んで
\((A/EA)_{\ge2}=0\) とできる。\(P=k[\lambda_1,\ldots,\lambda_r]\) と置き、以後この cut を変えない。
\(2\le r\le e-1\) であり、\(r\ge3\) なら \(a\ge a_r:=\binom{r+1}{2}\)。

\(F_s=F_sN\)、\(F_1=0\)、\(F_\nu=N\) とし、\(2\le s\le\nu\) で
\[
U_s=A/F_{s-1},\quad X_s=(U_s)_{\ge s},\quad
M_s=(U_s)_{\ge s+1},\quad K_s=F_s/F_{s-1}.
\]
すると実際の \(P\)-加群完全列
\[
0\longrightarrow K_s\longrightarrow M_s\longrightarrow X_{s+1}\longrightarrow0,
\qquad X_{\nu+1}=0 \tag{O5}
\]
が存在し、\(X_s,M_s\) はそれぞれ次数 \(s,s+1\) のみで極小生成される。
\[
h_{s,t}=\dim_k(X_s)_{s+t},\quad H_t=\sum_{s=2}^\nu h_{s,t},\quad S_H=\sum_{t\ge0}H_t
\]
は有限台を持ち、同じ一列について同時に
\[
\begin{gathered}
H_0=\delta,\qquad 0\le H_t\le M,\qquad S_H\le\delta\mathcal V,\\
H_1=\delta-a+\ell\le M-a,\qquad H_1\le r\delta,\\
r\ge3\Longrightarrow a_r\le a\le\delta,\quad H_1\le M-a_r,
\end{gathered} \tag{O6}
\]
が成り立つ。ここで \(\ell=\dim_k T_1\) は次数 1 の terminal 数である。

**証明。** Green の次数 2 の超平面制限定理の任意標数版を使う。
\(a=\binom{p+1}{2}+b\)、\(0\le b\le p\) なら、\(s\le p\) 本の一般形式による切断の二次元は
\(\binom{p+1-s}{2}+\max(b-s,0)\) 以下で、\(s=p\) で 0 となる。
標準生成性から高次も消える。\(p<2\) なら二本へ拡張する。
\(a\le\dim_k(S_0)_2=\binom e2\) より \(r\le e-1\) である。
体拡大による Betti 数の保存は自由解消の flat な scalar extension から従い、最後に元の体へ戻せる。

jump \(s\) の head の次数は少なくとも \(s+1\) だから \(K_s\subset M_s\)。また
\(U_s/K_s=U_{s+1}\) なので \(M_s/K_s=X_{s+1}\) となり (O5) を得る。
\(U_s\) は次数 \(s\) まで \(Q\) と一致し、square-zero cut により \(P\) 上次数 0,1 で生成される。
よって truncation は指定の単一次数で生成され、
\(\mu_P(X_s)=q_s\)、\(\mu_P(M_s)=h_{s,1}\) である。

資源の計数を明示する。次数 \(s_\rho\) の Apéry 座標が \(X_s\) に現れるのは
\(2\le s\le s_\rho\) で、\(H_t\) には区間 \([0,s_\rho-2]\) で一つずつ寄与する。
次数 \(p\) の terminal の jump を \(d\) とすると、次数 \(p+d\) の head は
\(2\le s\le d\) で現れ、区間 \([p,p+d-2]\) に寄与する。
同じ剰余の最初の terminal 次数は \(s_\rho\) 以上、次の terminal 次数は \(p+d\) 以上なので、これらの区間は互いに素である。
零剰余は寄与しない。従って \(H_t\le m-1\) であり、(O4) から
\[
S_H=\sum_{\rho\ne0}\left[(s_\rho-1)+\sum_{\tau\equiv\rho}(d(\tau)-1)\right]
=\sum_{\rho\ne0}(L_\rho-1)\le\delta\mathcal V.
\]
\(t=0\) は次数 2 以上の Apéry 元だけを数えるので \(H_0=\delta\)。
\(t=1\) は次数 3 以上の Apéry 元 \(\delta-a\) 個と、次数 1 の terminal \(\ell\) 個を数えるので
\(H_1=\delta-a+\ell\le\delta-a+e-1=M-a\)。
もう一方は \(h_{s,1}\le rq_s\) を足して得る。
\(\delta=0\) なら \(\nu=1,N=T=0\) で、塔・資源は空と読む。□

## 2.3　任意標数の調和評価

各多項式環 \(R\) 上で
\(b_i^R(Z)=\dim_k\operatorname{Tor}_i^R(Z,k)\)、
\(c_j^R(Z)=\sum_{i=0}^j(-1)^{j-i}b_i^R(Z)\) と書く。
有限生成 rank 0 加群の \(c_j\) は第 \(j+1\) syzygy の分数体上の rank なので非負である。

**補題 O4（調和 Koszul rank）。** \(P\) を \(r\) 変数多項式環、\(Z\) を次数 \(b\) のみで
極小生成される有限長加群、\(h_t=\dim_kZ_{b+t}\) とすると
\[
c_j^P(Z)\le\binom{r-1}{j}\sum_{t\ge0}\frac{j}{t+j}h_t\quad(1\le j<r),
\qquad c_0^P(Z)=\mu_P(Z),\quad c_r^P(Z)=0. \tag{O7}
\]

**証明。** shift を除き \(b=0\) とする。同 shift の表示 \(P^q\twoheadrightarrow Z\) の斉次核を \(K\) とし、
加群単項式順序を固定して \(Z^*=P^q/\operatorname{in}K=\bigoplus_aP/I_a\) を作る。
標準単項式は \(Z,Z^*\) 両方の次数別基底になる。
内部次数を固定し、Koszul 基底 \(m e_a\otimes e_F\) をラベル \(x_Fme_a\) 順に並べる。
normal form はラベルを上げないので境界は block 三角行列で、同一ラベルの対角 block は
\(Z^*\) の多重次数別境界そのものである。
各対角 block の最大 rank 小行列を結合すれば、行列式が非零対角小行列式の積となる。
従って、同じ体上で各境界の rank は \(R_i(Z)\ge R_i(Z^*)\) を満たす。

単項式商 \(P/I\) の次数 \(t\) の標準単項式を \(D_t\) とする。
\(\partial_{j+1}:Z_{t-1}\otimes\bigwedge^{j+1}k^r\to Z_t\otimes\bigwedge^jk^r\)
を多重次数 \(\alpha\)、\(|\alpha|=t+j\) に分ける。
target 行は \((m,F)\)、\(|F|=j\)、\(m=\alpha-\mathbf1_F\in D_t\)。
\(v\in\operatorname{supp}\alpha\) を固定し、\(v\notin F\) の行に source 列
\((m/x_v,F\cup\{v\})\) を割り当てる。
\(m_v=\alpha_v>0\) かつ標準単項式の約数も標準なので、この列は存在する。
この列の \(v\) を消す成分だけが選んだ行に入り、他の成分は wedge に \(v\) を含む。
従って選択小行列は対角 \(\pm1\) であり、任意標数で
\(R_\alpha\ge\#\{(m,F):v\notin F\}\) である。

これを有理数重み \(\alpha_v/(t+j)\) で平均し、\(\alpha\) について足すと
\[
\operatorname{rank}\partial_{j+1}\ge\frac1{t+j}
\sum_{m\in D_t}\sum_{|F|=j}\sum_{v\notin F}m_v
=\binom{r-1}{j}\frac{t}{t+j}|D_t|.
\]
\(t=0\) の下界は 0 と読む。ここで平均しているのは整数 rank の数値であり、係数体で \(t+j\) を割っていない。
全境界 rank を \(R_i\)、\(\lambda=\operatorname{length}Z\) と書けば
\[
b_i=\binom ri\lambda-R_i-R_{i+1},\qquad
c_j=\binom{r-1}{j}\lambda-R_{j+1}.
\]
初項化の rank 比較と上の下界を足し合わせれば (O7) が従う。
\(c_0=\mu\) は定義、\(c_r=0\) は有限長の rank Euler 恒等式である。□

## 2.4　同じ塔から全相対 rank へ

以下の \(c_j(G)\) は \(R=k[x,E]\) 上の値とする。

**補題 O5（Tor の三段鎖）。** \(1\le j\le r\) について
\[
c_j(G)\le L_j+\sum_{t\ge0}W_j(t)H_t,\qquad
L_j=(e-1)\binom{r-1}{j}-\binom{r-1}{j+1}, \tag{O8}
\]
ただし
\[
\begin{gathered}
W_1(0)=r-1,\qquad W_1(1)=(r+1)/2,\qquad W_1(t)=(r-1)/(t+1)\ (t\ge2),\\
W_j(0)=\binom{r-1}{j},\qquad
W_j(t)=\frac{j\binom{r-1}{j}}{t+j}
+\frac{(j-1)\binom{r-1}{j-1}}{t+j-2}\quad(2\le j\le r,\ t\ge1).
\end{gathered}
\]

**証明。** 完全列 \(0\to K\to M\to L\to0\) の connecting rank を \(d_i\) とすると
\[
c_j(M)=c_j(K)+c_j(L)-d_{j+1},\quad
c_j(K)=c_j(M)+c_{j+1}(L)-[b_{j+1}(L)-d_{j+1}]. \tag{O9}
\]
減算する \(d_{j+1}\) とその補数はともに非負である。
\(x\)-Koszul homology は \(A,T\) の 0,1 行だけであり、唯一の後続微分
\(d_2:\operatorname{Tor}_i^P(A,k)\to\operatorname{Tor}_{i-2}^P(T,k)\) の rank を \(\rho_i\) と書くと
\[
b_i^R(G)=b_i^P(A)+b_{i-1}^P(T)-\rho_i-\rho_{i+1},\qquad
c_j(G)=c_j^P(A)+c_{j-1}^P(T)-\rho_{j+1}. \tag{O10}
\]
次数 shift は total 次元を変えない。微分の消滅は仮定しない。
低次数商は
\(B=A/X_2\simeq P/P_+^2\oplus k(-1)^{e-r-1}\)、従って \(c_j^P(B)=L_j\) である。
ここで短完全列、(O2)、(O5) を順に使うと
\[
\begin{aligned}
c_j(G)&\le L_j+c_j^P(X_2)+c_{j-1}^P(T),\\
c_{j-1}^P(T)&\le\sum_{s=2}^{\nu}c_{j-1}^P(K_s),\\
c_{j-1}^P(K_s)&\le c_{j-1}^P(M_s)+c_j^P(X_{s+1}).
\end{aligned} \tag{O11}
\]
第 2 行では逆向き filtration の同 jump stratum のみを同定している。
\(X_{\nu+1}=0\) なので \(X_s\) 項はちょうど一巡する。
\(j=1\) では \(\sum_s c_0^P(M_s)=\sum_s\mu_P(M_s)=H_1\) を正確に使い、
\(j\ge2\) では (O7) を使う。
\(M_s\) の Hilbert 列は \(X_s\) の一段先から始まるので第二項の分母は
\((t-1)+(j-1)=t+j-2\) である。
これで (O8) を得る。top の \(j=r\) でも有限長 \(P\)-加群の \(c_r=0\) を使えば同じ式になる。□

## 2.5　actual ordinary target への一回の移行と差分による容量

ここから物理幅 \(g_e-m\ge m-1\) を仮定する。
literal interval completion は \(\langle m,m+1,\ldots,2m-1\rangle\) であり、
算術列公式と接錐一致の任意体版から、その Betti 多項式は
\[
T_m(z)=1+\sum_{i\ge1}i\binom m{i+1}z^i
\]
である。

**補題 O6（第 0 homology を補正した全行移行）。**


\(q=e-r\)、\(N_*=\delta+r-1=m-q-1\) と置き、
\[
R_j(\delta)=(q+j)\binom{\delta+r-1}{j}+j\binom{\delta+r-1}{j+1}.
\]
\(c_j(G)\le R_j(\delta)\ (1\le j\le r)\) なら、各環自身の最小表示環で全 \(i\ge0\) の Betti 比較が成り立つ。
そのための容量下界は
\[
R_j(\delta)-L_j\ \ge\ \delta(\mathcal V+1)\binom{r-1}{j-1}
\qquad(j\ge1). \tag{O12}
\]

**証明。** \(E\) を非 \(x\) 一次空間の基底へ拡張し、残る \(f=e-r-1=q-1\) 変数を \(Z\) とする。
\(G\) は \(R=k[x,E]\) 上有限生成 rank 0、極小生成元数 \(q\) である。
\(C(z)=\sum_{j=1}^rc_j(G)z^j\) とすれば相対 Betti 多項式は
\(\mathcal B_G^R=(1+z)(q+C(z))\) となる。
\(H_0(K_R(G))=G/(x,E)G\cong k[Z]/(Z)^2\) の Betti 多項式は正確に \(T_q\)。
二重複体でこの 0 行だけを正確に評価し、正の行を \(Z\)-Koszul 鎖群で抑えると
\[
\begin{aligned}
\mathcal B_G
&\preceq T_q+(1+z)^{q-1}(\mathcal B_G^R-q)\\
&=T_{q+1}+(1+z)^qC(z).
\end{aligned} \tag{O13}
\]
引く定数 \(q\) が第 0 homology の補正である。
最後の等式には \(T_{q+1}-T_q=qz(1+z)^{q-1}\) を使った。
後続微分は total homology 次元を減らすので退化を仮定しない。

同じ一階差分を \(m\) まで足せば
\[
\begin{aligned}
T_m-T_{q+1}
&=(1+z)^q\sum_{a=0}^{N_*-1}(q+1+a)z(1+z)^a\\
&=(1+z)^q\sum_{j=1}^{N_*}R_j(\delta)z^j.
\end{aligned} \tag{O14}
\]
係数恒等式は hockey-stick と
\(a\binom a{j-1}=(j-1)\binom a{j-1}+j\binom aj\) による。
\(j>r\) の target 係数は非負のまま余るので、指定した \(r\) 個の比較で全 Betti 行を払える。
\(\delta=0,N_*=r-1\) のときも範囲外二項係数を 0 とすれば \(R_r=0\) を含む。

容量下界には完全な Vandermonde 余剰式は不要である。
Pascal と \(j\binom nj=(n-j+1)\binom n{j-1}\) から直接
\[
R_j(0)=L_j,\qquad
R_j(d+1)-R_j(d)=(e+d)\binom{d+r-1}{j-1}
\ge(e+d)\binom{r-1}{j-1}.
\]
\(d=0,\ldots,\delta-1\) を足すと
\[
R_j(\delta)-L_j\ge
\left[e\delta+\frac{\delta(\delta-1)}2\right]\binom{r-1}{j-1}
=\delta(\mathcal V+1)\binom{r-1}{j-1}.
\]
これが (O12) であり、top や \(\delta=0\) を特別に除かない。□

## 2.6　二本・三本の cut と一つの scalar

**補題 O7（低 rank と全 rank の scalar 化）。**


actual cut が \(r=2,3\) なら \(c_j(G)\le R_j\) が全 \(1\le j\le r\) で成り立つ。
\(r\ge4\) では同じ資源列について
\[
F_r=(r-1)\delta+\frac{r+1}{2}H_1+\sum_{t\ge2}\frac{r-1}{t+1}H_t
\]
と置くと、top を含めて
\[
c_j(G)\le L_j+\binom{r-1}{j-1}F_r\qquad(1\le j\le r). \tag{O15}
\]
従って必要なのは \(F_r\le\delta(\mathcal V+1)\) だけである。

**証明。** \(r=2\) では (O8) と同じ列の
\(H_1\le S_H-\delta\)、\(H_1\le2\delta\) をそれぞれ使って
\[
c_1-L_1\le\min\{\tfrac32S_H-\tfrac12\delta,
\ \tfrac52\delta+\tfrac12S_H\}.
\]
前者は \(\mathcal V\le3\)、後者は \(\mathcal V\ge3\) で
\(\delta(\mathcal V+1)\) 以下となる。
top は \(c_2\le\sum_{t\ge1}H_t/t\le S_H-\delta\) で払える。
\(\delta=0\) の空塔も含まれる。

\(r=3\) なら \(e\ge4\)、\(a\ge6\)、\(\delta\ge6\)、\(\mathcal V\ge11/2\) である。
第一 rank の \(t\ge2\) の重みは \(2/3\) 以下なので
\[
c_1-L_1\le\tfrac43\delta+\tfrac43H_1+\tfrac23S_H.
\]
\(H_1\le M-6\) を使った容量との差の 3 倍は
\(\delta(\mathcal V-1)-4(M-6)\)。
\(z=\delta-6\)、\(s=e-4\) とすると、この値は
\(zs+z^2/2+7z/2+2s+15>0\) である。
第二 rank は \(W_2(0)=1\)、\(W_2(1)=8/3\)、
\(W_2(t)=2/(t+2)+2/t\le3/2\ (t\ge2)\) と \(H_1\le3\delta\) より
\[
c_2-L_2\le\tfrac32S_H-\tfrac12\delta+\tfrac76H_1
\le\tfrac32S_H+3\delta
\le2\delta(\mathcal V+1).
\]
最後は \(\delta(\mathcal V/2-1)\ge0\)。top は
\(W_3(t)=2/(t+1)\le1\ (t\ge1)\)、\(W_3(0)=L_3=0\) から \(c_3\le S_H-\delta\) である。

\(r\ge4\) では \(j\ge2\) の重みを \(\binom{r-1}{j-1}>0\) で割る。
\(j\binom{r-1}{j}=(r-j)\binom{r-1}{j-1}\) より
\[
\frac{W_j(0)}{\binom{r-1}{j-1}}=\frac{r-j}{j}\le r-1,\qquad
\frac{W_j(1)}{\binom{r-1}{j-1}}=\frac{r+1}{j+1}\le\frac{r+1}{2}.
\]
\(t\ge2\) の正規化重みは
\((r-j)/(t+j)+(j-1)/(t+j-2)\)。
\(j\ge3\) なら両分母は \(t+1\) 以上で、和は \((r-1)/(t+1)\) 以下。
\(j=2\) ではその上界との差は
\([2-(r-3)t]/[t(t+1)(t+2)]\le0\) である。
全ての \(H_t\) が非負なので (O15) を得る。□

## 2.7　固定 cutoff の差を一度だけ計算する

**補題 O8（共通 cutoff 恒等式）。** \(r\ge4\)、\(a=a_r\)、整数 \(n\ge r\) を固定し、
\[
\alpha=\frac{r-1}{n+1},\quad \beta=1-\alpha,\quad
\mathcal H_n=\sum_{j=1}^n\frac1j,\quad c=\frac{r+1}{2}-\alpha
\]
と置く。(O6) の同じ資源列に対し
\[
\begin{aligned}
F_r\le U(e,\delta)={}&\alpha\delta\mathcal V+(r-1-\alpha)\delta+c(M-a)\\
&+M\sum_{j=2}^{n-1}\left(\frac{r-1}{j+1}-\alpha\right).
\end{aligned} \tag{O16}
\]
\(G(e,\delta)=\delta(\mathcal V+1)-U(e,\delta)\) とし、任意の基点 \(e_0\) に対し
\[
g=G(e_0,a),\quad
A=a-1-(r-1)\left(\mathcal H_n-2+\frac{a+2}{n+1}\right),\quad
b=G(e_0,a+1)-G(e_0,a)
\]
と置けば、任意の有理数 \(s,t\) に対して
\[
\boxed{G(e_0+s,a+t)=g+sA+tb+\beta\left(\frac{t(t-1)}2+st\right).} \tag{O17}
\]

**証明。** \(F_r\) の各重みから \(\alpha\) を引く。\(t=0,1\) はそれぞれ
\(H_0=\delta\)、\(H_1\le M-a\) を使う。
\(2\le t<n\) の残余係数は正なので \(H_t\le M\) を使い、\(t\ge n\) では非正なので捨てる。
共通部分には \(\sum H_t\le\delta\mathcal V\) を用いる。
これが (O16) であり、資源列の台が cutoff より手前にあるとは仮定していない。
有限和を足すと
\[
U=M+(r-1)\left[\delta+\frac{\delta(\mathcal V-1)}{n+1}
+M\left(\mathcal H_n-2+\frac2{n+1}\right)\right]-ca.
\]
従って \(G\) は \(e\) の一次式で、その係数は
\(A(\delta)=\delta-1-(r-1)(\mathcal H_n-2+(\delta+2)/(n+1))\)。
\(A(a+t)=A+\beta t\)、また \(\delta\) の二次係数は \(\beta/2\) である。
基点の一階差分を \(b\) とすれば
\(G(e_0,a+t)=g+tb+\beta t(t-1)/2\) となり、\(sA(a+t)\) を加えて (O17) を得る。
これは有理係数の多項式恒等式である。正値性に使うときの \(s,t\) の範囲は以下で別に指定する。□

## 2.8　小 rank：actual Apéry–Sidon と五行の厳密算術

**補題 O9（最大二次層の実現条件）。**
\[
q_2=\binom e2\quad\Longrightarrow\quad m\ge e(e-1)+1,
\qquad\delta\ge(e-1)^2. \tag{O18}
\]

**証明。** 非 \(m\) 生成元に対応する二次単項式は \(\binom e2\) 個で、\(Q_2\) へ全射する。
次元が等しいなら、全二次単項式は相異なる次数 2 の非零 Apéry 座標を与える。
\(B=\{0,\overline g_2,\ldots,\overline g_e\}\subset\mathbb Z/m\mathbb Z\) と置く。
異なる Apéry 元は異なる剰余を持つので、二次積の剰余同士は異なり、
次数 0 の 0、次数 1 の原子の剰余とも一致しない。
従って \(B\) の順序を無視し反復を許す全二項和は相異なる。
\(b-c=b'-c'\) なら \(b+c'=b'+c\) なので、二項和の一意性から
\((b,c)=(b',c')\) または \(b=c\) となる。
ゆえに非対角順序対から非零剰余への差写像は単射で、\(e(e-1)\le m-1\) を得る。□

actual cut で \(r=e-1\) かつ \(r\ge3\) なら
\(q_2\ge a_r=\binom e2\) なので上の補題が適用できる。
\(r^2>a_r\) だから、\(e=r+1,\delta=a_r\) という角は実現しない。
この cut からの含意には \(r=2\) を含めない。

**補題 O10（\(4\le r\le8\)）。** actual 資源列について \(F_r<\delta(\mathcal V+1)\) である。

**証明。** (O17) で \(e_0=r+1\)、\(s=e-r-1\)、\(t=\delta-a_r\) と置く。
これらは非負整数であり、\(b=A+2-\alpha(r-1)\) である。
各 rank で次の固定 cutoff を使う。最後の三列は共通の正分母 \(L\) を持つ厳密な値である。

| \(r\) | \(a_r\) | \(n\) | \(L\) | \(Lg\) | \(LA\) | \(Lb\) |
|---:|---:|---:|---:|---:|---:|---:|
|4|10|7|280|2443|762|1007|
|5|15|10|6930|39380|28429|32209|
|6|21|13|72072|−7479|424147|439591|
|7|28|17|2042040|−12196485|17076937|17076937|
|8|36|21|739024|−5070732|8418651|8250691|

この表は (O16) の有限有理和を足した値であり、新たな幾何学的仮定を含まない。
全行で \(A,b,\beta>0\)。\(r=4,5\) は \(g>0\) なので (O17) は正。
\(r=6,7,8\) は \(g+A>0\)、\(g+b>0\) なので \(s+t\ge1\) なら正。
非負整数 \(t\) に対して \(t(t-1)/2\ge0\) を使った。
残る \(s=t=0\) は (O18) によって実現しない。
従って全 actual source で \(G>0\) となり、(O16) から結論を得る。
無限域の根拠は (O17) であり、有限点からの外挿ではない。□

## 2.9　大 rank：一つの調和障壁と一つの床比較

**補題 O11（大 rank）。** 整数 \(r\ge9\)、\(e\ge10\)、\(\delta\ge a_r\) で
同じ資源列の \(F_r<\delta(\mathcal V+1)\) が成り立つ。

**証明。** \(a=a_r=r(r+1)/2\)、\(D=\lfloor a/2\rfloor+1\)、
\(\alpha=(r-1)/(D+1)\)、\(\beta=1-\alpha\) と置く。
補題 O8 の cutoff を \(n=D\) とし、そこで定義した上界と差を
\(U_r(e,\delta),G_r(e,\delta)\) と書く。
\(D\ge r\) なので \(0<\alpha<1\)、\(\beta>0\) である。
以下の正値性は有理数 \(e\ge10,\delta\ge a\) にも成立する。

**調和障壁。** \(a_r=r(r+1)/2\)、\(D_r=\lfloor a_r/2\rfloor+1\)、
\(B(r)=r/4+1+9/(2r)\) と置く。床の両側評価は
\[
a_r+1\le2D_r\le a_r+2. \tag{OL2}
\]
\(b=D_{r+1}-D_r\) について、\(a_{r+1}=a_r+r+1\) と (OL2) から
\(b\ge0\)、\(2b\le r+2\)、\(2(D_r+1)\ge a_r+3\) を得る。
従って、増分の各項をその最初の項で抑えるだけで
\[
H_{D_{r+1}}-H_{D_r}
\le\frac{b}{D_r+1}\le\frac{r+2}{a_r+3}. \tag{OL3}
\]
\(r\ge10\)、\(x=r-10\ge0\) で、通分した恒等式は
\[
B(r+1)-B(r)-\frac{r+2}{a_r+3}
=\frac{x^4+34x^3+385x^2+1472x+112}
 {4r(r+1)(r^2+r+6)}>0. \tag{OL4}
\]
初期値 \(D_{10}=28\) における正確な差は
\[
B(10)-H_{28}=\frac{1833472237}{80313433200}>0.
\]
(OL3)–(OL4) を足す帰納法により、全 \(r\ge10\) で
\(H_{D_r}<B(r)\) が従う。凸性補題も、中間上界 \(2/r\) も不要である。

**seed の正値性。** \(D=D_r\) とし
\[
T_r=\frac{a(a+22-r)}{2(r-1)(a+9)}
+\frac{2r-3}{r-1}
-\frac{a(a+21)+36}{2(D+1)(a+9)}.
\]
(O16) の有限和を整理すると
\[
g_0:=G_r(10,a)=(r-1)(a+9)(T_r-H_D). \tag{OL5}
\]
\(T_-(r)\) を \(T_r\) の最後の分母 \(2(D+1)(a+9)\) を
\((a+3)(a+9)\) に置き換えた式とする。(OL2) より
\(T_-(r)\le T_r\)。さらに
\[
T_-(r)-B(r)=
\frac{N(r)}{2r(r-1)(r^2+r+6)(r^2+r+18)}>0
\quad(r\ge10), \tag{OL6}
\]
ここで
\[
N(r)=r^3[(r-10)(2r+15)+2]+r[111(r-10)+210]+972>0.
\]
よって \(H_D<B(r)<T_-(r)\le T_r\) から \(g_0>0\)。
残る \(r=9\) は \(a=45,D=23\) を (O16) に入れた正確な値
\[
G_9(10,45)=\frac{5845533}{7436429}>0
\]
で閉じる。この一つの seed を越える rank に有限検算は使っていない。

**二方向への延長。**
\[
\begin{gathered}
A=G_r(11,a)-G_r(10,a),\quad
b_0=G_r(10,a+1)-G_r(10,a),\\
C=\frac{a[-a(D-r+2)-D(r-4)+3]}{2(D+1)}.
\end{gathered}
\]
(O16) から得る恒等式は
\[
g_0=(a+9)A+C,\qquad b_0=A+11-r-8\alpha. \tag{OL7}
\]
\(r\ge9\) では \(a\ge4r\)、\(D\ge r\) であり、\(C\) の角括弧は
高々 \(-2a+3<0\)。従って \(C<0\)、
\(A>-C/(a+9)>0\)。ここで
\[
\begin{aligned}
F(D)&=-C/(a+9)+11-r-8\alpha,\\
F_{\min}&=\frac a2-\frac{3r}2+\frac{11}2
+\frac{3(5r+31)}{2(a+9)}-\frac{17(r-1)}{a+3}
\end{aligned}
\]
と置くと、偶奇を分けずに
\[
F(D)-F_{\min}=
\frac{(2D-a-1)(r-1)(a^2+17a+144)}
 {2(a+9)(D+1)(a+3)}\ge0. \tag{OL8}
\]
分子の \(2D-a-1\) は (OL2) により非負である。また \(a\ge4r\) から
\[
\frac a2-\frac{3r}2+\frac{11}2\ge\frac{11}2,
\qquad \frac{r-1}{a+3}<\frac14.
\]
正の残余項もあるので
\(F_{\min}>11/2-17/4=5/4\)。従って
\(b_0>F(D)\ge F_{\min}>5/4\)。

\(0<\alpha<1\)（\(D\ge r\) より）、\(\beta=1-\alpha\) とすると、
任意の有理数 \(s,t\ge0\) に対して、共通差分恒等式 (O17) を
\(e_0=10\) で整理すると
\[
G_r(10+s,a+t)
=g_0+sA+t(b_0-\beta/2)+\beta(t^2/2+st)>0. \tag{OL9}
\]
各非定数項は非負、定数 \(g_0\) は正である。
この書き方では \(t(t-1)\ge0\) を仮定せず、床の偶奇の場合分けも使わない。
従って同じ資源列の \(F_r\le U_r(e,\delta)\) と合わせて
\(F_r<\delta(\mathcal V+1)\) を得る。相対 rank の scalar 化と actual target の
係数恒等式へ戻れば、ordinary の \(r\ge9\) 枝の全 Betti 行が閉じる。



## 2.10　ordinary 枝の全域閉鎖

**定理 O12。** 任意体 \(k\)、真正な最小生成系を持つ \(e\ge3\) の数値半群 \(S\) で
\(g_e-m\ge m-1\) なら、各環自身の最小表示環について
\[
\beta_i(G_S;k)\le\beta_i(G_{\widetilde S};k)
=i\binom m{i+1}\quad(i\ge1),\qquad \beta_0(G_S;k)=\beta_0(G_{\widetilde S};k)=1.
\]

**証明。** O1–O3 で元の source から一つの actual cut と一つの資源列を構成し、
O4–O5 でその全相対 rank を評価する。必ず \(2\le r\le e-1\)。
\(r=2,3\) は O7 で閉じる。\(4\le r\le8\) は O9–O10、\(r\ge9\) は
\(e\ge r+1\ge10\) と O11 によって必要な scalar 不等式を得て、O7 を通して全相対 rank を閉じる。
全枝を O6 に入れれば全 Betti 行が得られる。
相対 top \(j=r\) は O5、O7 に含み、\(j>r\) の target 係数は O14 で非負に余る。
source の \(i>e\) 行は Hilbert syzygy により 0、第 0 行は両側 1 である。
必要に応じて最初に行った同標数の純超越拡大を flat scalar extension による Betti 保存で戻す。
異なる標数の rank 一致は一切使わない。□

この経路に first-hit、truncated lex、83 profile・665 比較・5 infinite tail は現れない。
それらを付録へ移して必要性を隠すのではなく、主定理への数学的依存から除いている。
三生成元の narrow 部分および \(e=1,2\) は全体合成の別枝で扱う。
