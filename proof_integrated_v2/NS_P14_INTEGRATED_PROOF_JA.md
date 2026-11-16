# NS-P14：簡約を統合した単一証明稿 V02

2026年11月9日。論文化・Lean形式化に先立つ数学的作業稿。

## 1 主張・記号・公刊入力

### 1.1 比較する環と証明の構成

\(\Gamma=\langle m=g_1<\cdots<g_e\rangle\) を真正な最小生成系を持つ数値半群、
\(k\) を任意の体とする。\(\mathfrak m\subset k[[t^\Gamma]]\) を極大イデアルとし、
\[
G_\Gamma=\operatorname{gr}_{\mathfrak m}k[[t^\Gamma]],\qquad
\widetilde\Gamma=\langle m,m+1,\ldots,g_e\rangle
\]
と置く。各環をそれぞれの最小生成系に対応する多項式環で表示し、total graded
Betti数を \(\beta_i(G_\Gamma;k)\) と書く。証明する主張は
\[
\boxed{\beta_i(G_\Gamma;k)\le
       \beta_i(G_{\widetilde\Gamma};k)\quad(i\ge0).}\tag{P14}
\]
第0行は双方1。負の下添字、または上添字を超える下添字の二項係数は0とする。

物理幅を \(w=g_e-m\) とし、\(e\ge2\) では \(d=\gcd(g_2-m,\ldots,g_e-m)\)、正規化幅を \(u=w/d\)
とする。\(w\ge m-1\) ではcompletionは
\(\langle m,m+1,\ldots,2m-1\rangle\) に等しい。この領域をordinary側と呼び、
第2–11節と第15節で扱う。\(w\le m-2\) では第12節の共通端点補題を用い、
\(e\ge5\) を第13節、\(e=4\) を第14節で扱う。残る \(e\le3\) を含め、
第16節で全場合を合成する。

ordinary側では \(\delta=m-e\)、\(M=m-1\)、
\(\mathcal V=e+\delta/2-3/2\) を資源量に使う。\(\mathcal V\) は幅ではない。
端点法では \(Q_C=C/(x,v)C,\ P_C=\dim Q_C\) と、
\(Q_G=G/(x,v)G,\ P_G=\dim Q_G\) を区別する。二変数の場合の
\(\sigma_C\) は \(Q_C\) の内部socle次元、\(R=\dim(0:_G(x,v))\) はactual接錐の
端点socle次元である。体の標数が変わってもactual Betti数が不変とは仮定しない。

### 1.2 使用する公刊定理

以下を外部の数学的入力として使用する。これらの定理そのものを本稿で再証明する
という意味ではない。以後の独自補題と有限化は本文中で証明する。

1. **Greenの超平面制限定理。** 無限体上の標準次数付き代数 \(B\) に対し、
   一般一次形式による次数別Hilbert関数のMacaulay下降上界を用いる。
   本稿で必要なのは次数2のみで、第4節にその具体形を記す。
   [Caviglia, A hyperplane restriction theorem and applications to reductions of ideals,
   §1, (1.1)](https://www.math.purdue.edu/~gcavigli/Articles-PDF/%5BS4%5D.pdf)。
   同所は任意標数の原Green定理を扱う。有限体は第4節で同標数の純超越拡大により処理する。
2. **BHPとEliahou–Kervaire。** 同じHilbert関数を持つlex商は任意の斉次商の
   各graded Betti数を上から抑える。lex理想 \(L\subset k[X_1,\ldots,X_q]\) の
   極小単項式生成元 \(v\) は、商の第 \(i\ge1\) 行へ
   \(\binom{\max(v)-1}{i-1}\) を寄与する。
   任意体版の正確な再掲は
   [Juhnke-Kubitzke–Venturello, Graded Betti Numbers of Balanced Simplicial Complexes,
   §2.2, Lemmas 2–3](https://link.springer.com/article/10.1007/s40306-021-00449-8)。
   BHPはBigatti–HulettにPardueの正標数版を含めた定理である。
3. **Kneserの加法定理。** 有限非空部分集合 \(A,B\) と
   \(H=\operatorname{stab}(A+B)\) に対して
   \(|A+B|\ge|A+H|+|B+H|-|H|\)。
   [DeVos, A short proof of Kneser's addition theorem for abelian groups,
   Theorem 1](https://www.sfu.ca/~mdevos/papers/kneser.pdf)。
   本稿では有限巡回群に適用し、合成数位数も許す。
   \(H=\operatorname{stab}(nA)\) について商群で反復すると
   \(|nA|\ge n|A+H|-(n-1)|H|\) を得る。
   実際、商群内の部分和のstabilizerは全和のstabilizerに含まれるため自明であり、
   二集合版を各段階へ適用できる。
4. **算術列のBetti公式と接錐一致。**
   [Gimenez–Sengupta–Srinivasan, arXiv:1108.3203, Theorem 4.1](https://arxiv.org/pdf/1108.3203)
   と [Herzog–Stamate, arXiv:1308.4644v3, Proposition 2.5](https://arxiv.org/pdf/1308.4644)。
   前者は任意体上の算術列半群環の公式、後者は算術列の定義理想とその接錐理想の
   Betti一致を与える。具体的な比較容量は次小節に固定する。
5. **三生成元の場合。**
   [Lan–Tu–Vu, Betti numbers of the tangent cones of monomial space curves,
   Theorem 1.1](https://arxiv.org/html/2307.05589v1#S1)。
   三生成元・任意体についてactual interval completionとのBetti比較を用いる。
   理想のBettiから商の正のBettiへは添字を1ずらし、第0行1を補う。
6. **Savchev–Chenの零和のない列の定理。**
   [Long zero-free sequences in finite cyclic groups, §4, Theorem 8](https://arxiv.org/html/math/0602568v1)。
   位数 \(u\) の巡回群で零和のない列の長さが \(u/2\) を超えるなら、あるunitを
   全項に掛けた後の正の代表値の総和を \(u\) 未満にできる。第14節の混合語にのみ使う。

Koszul複体、Tor長完全列、Hilbert syzygy、自由解消のrank Euler恒等式、
有界二重複体のスペクトル系列、およびGröbner除法は通常の代数的道具として用いる。
後の頁によるhomology次元の減少を利用し、スペクトル系列の退化は仮定しない。

### 1.3 Actual intervalの容量

ここでは \(m\ge2\) とする。\(m=1\) は第16節で直接扱う。
\(V_{\mathrm{tar}}=\min(w,m-1)\ge1\) とする。completionの最小生成系は正確に
\(m,m+1,\ldots,m+V_{\mathrm{tar}}\) である。
\(D=V_{\mathrm{tar}}-((m-1)\bmod V_{\mathrm{tar}})\in\{1,\ldots,V_{\mathrm{tar}}\}\)
と置くと、第1.2節の算術列公式は
\[
F_i(m,V_{\mathrm{tar}})
=i\binom{V_{\mathrm{tar}}}{i+1}+
\begin{cases}
(D+1-i)\binom{V_{\mathrm{tar}}}{i-1},&i\le D,\\
(i-D)\binom{V_{\mathrm{tar}}}{i},&i>D
\end{cases}\qquad(i\ge1).\tag{TAR}
\]
ここで元の公式の \(m=aV_{\mathrm{tar}}+b,\ 1\le b\le V_{\mathrm{tar}}\)
に対して \(D=V_{\mathrm{tar}}-b+1\) である。
理想から商への添字もこの式に合わせる。
第0行は1、\(i>V_{\mathrm{tar}}\) は0とする。
剰余パラメータについての最小値は
\[
F_i^{\min}(v)=i\binom v{i+1}
 +\min\!\left\{\binom v{i-1},\binom vi\right\}\quad(1\le i\le v).\tag{TMIN}
\]
両候補は \(D=i\) または \(D=i-1\) の境界で得られ、端の行は直接同じ式となる。
各二項係数は上添字について非減少なので、各行の \(F_i^{\min}(v)\) も非減少である。
範囲外の行は0と読む。

特にordinary targetでは \(v=m-1,D=v\) なので
\[
\beta_i(G_{\widetilde\Gamma})=i\binom m{i+1}\quad(i\ge1).\tag{ORD}
\]
狭幅で使う下界は
\[
\begin{aligned}
F_1(m,v)&\ge\binom v2+1,\\
F_2(m,v)&\ge2\binom v3+v &&(v\ge3),\\
F_3(m,v)&\ge3\binom v4+\binom v2 &&(v\ge5),\\
F_4(m,v)&\ge4\binom v5.
\end{aligned}\tag{TLOW}
\]
第2行の補正は \(D\ge2\) なら少なくとも \(v\)、\(D=1\) なら \(\binom v2\ge v\)。
第3行は \(D\ge3\) で少なくとも \(\binom v2\)、\(D=2\) で
\(\binom v3\ge\binom v2\)、\(D=1\) ではさらに大きい。
したがって比較先を正規化した仮想の半群へ取り換える必要はない。

## 2 数値座標と非Apéry部分

\(\operatorname{ord}(v)\) を \(v\in\Gamma\) の最長生成元表示の長さとする。\(G\) は \([v]\) という数値座標基底を持ち、その次数は \(\operatorname{ord}(v)\) である。積は次数が加法的なとき \([v+w]\)、それ以外は0となる。

\[
 x=[m],\qquad A=G/xG,\qquad T=(0:_Gx),
 \qquad S_0=k[Y_1,\ldots,Y_{e-1}].
\]

\(A\) の基底は、\(x\) の生きた矢印が入ってこない座標、すなわちx-headである。数値Apéry集合
\(\operatorname{Ap}(\Gamma,m)=\{\omega_\rho:0\le\rho<m\}\)
以外のx-headの張る部分を \(N\subset A\) とする。非x生成元による生きた積は、前駆元の存在を保つから、\(N\) は **\(S_0\) 全体に関する斉次イデアル**である。

\(T\) の基底座標 \(\tau\) は、死んだx矢印の始点である。対応する非Apéry headは \(\tau+m\) であり、

\[
 d(\tau)=\operatorname{ord}(\tau+m)-\operatorname{ord}(\tau)\ge2.
\]

\(\tau\) は正なので、そのheadの次数は少なくとも3である。
\(\tau\mapsto\tau+m\) は基底の全単射である。**\(T\) と \(N\) 全体の加群同型は使わない。**

\[
 Q=A/N,\qquad q_s=\dim_k Q_s,\qquad
 \nu=\max\{s:Q_s\ne0\},\qquad a=q_2.
\]

\(Q\) は数値Apéry基底を持つ標準次数付きArtin代数であり、

\[
 \operatorname{length}Q=m,\quad q_0=1,\quad q_1=e-1,
 \quad\sum_{s\ge2}q_s=\delta,\quad
 A_2=Q_2,\quad0\le a\le\delta. \tag{2.1}
\]

標準生成から \(\nu\le\delta+1\) である。

生きた \(T\)-矢印ではjumpは非減少、生きた \(N\)-矢印では非増加である。実際、\(\sigma=\tau+g_i\) とすると、前者では
\(\operatorname{ord}(\sigma+m)\ge\operatorname{ord}(\tau+m)+1\)、後者では
\(\operatorname{ord}(\sigma)+d(\sigma)=\operatorname{ord}(\tau)+d(\tau)+1\)
を使えばよい。jumpが等しいとき、両側の生きた作用は一致する。

したがって \(N\) はjumpの昇順、\(T\) は降順の \(S_0\)-加群filtrationを持つ。等jumpのstratumで、headの次数 \(p+s\) とterminalの次数 \(p\) が対応する。total Torに対してこの次数差は影響しない。

すべてのjumpは \(d\le\nu\) を満たす。これを確認するため \(Q=S_0/I_Q\)、\(A=S_0/I_A\) と書く。\(Q_{\nu+1}=0\) なので \(I_Q\) は次数 \(\nu+1\) 以下で生成され、\(N=I_Q/I_A\) も同じ次数上界を持つ。極小headの次数は高々ν+1であり、対応するterminalの次数は少なくとも1なので、そのjumpは \(\nu\) 以下であり、以後の生きた \(N\)-作用ではjumpが増えない。これですべてのhead、したがってすべてのterminalに上界が伝播する。

## 3 最短offset経路だけで総量を評価する

必要な総量上界を最短offset経路から証明する。
各剰余 \(\rho\bmod m\) に対し、正offset \(g_i-m\ (i>1)\) の和の最小値を \(b_\rho\)、それを与える最短語長を \(l_\rho\) とする。\(b_0=l_0=0\) とし、
\[
 s_\rho=\operatorname{ord}(\omega_\rho),\qquad
 L_\rho=(\omega_\rho-b_\rho)/m.
\]
非零剰余では \(1\le s_\rho\le L_\rho\le l_\rho\)。最長のApéry表示のoffsetは \(b_\rho\) 以上であり、least-offset語の数値重み \(b_\rho+ml_\rho\) は \(\omega_\rho\) 以上だからである。

**経路補題。** 非零剰余を \(b_\rho\) の昇順に \(\rho_1,\ldots,\rho_{m-1}\) と並べると
\[
 L_{\rho_k}-1\le\min(\delta,k-1). \tag{3.1}
\]

**証明。** 非xのactual atomはそれぞれApéry元であり、その剰余は相異なる。同じ剰余の二つのatomの大きい方は小さい方と \(m\) の正の倍数に分解されてしまう。したがってatom剰余は \(e-1\) 個、残る非零剰余は \(\delta\) 個である。

least-offset語の各prefixもleast-offset語である。より小さいprefixへ置き換えれば語全体のoffset最小性に反する。prefix剰余も相異なる。同じ剰余を二度通れば、その間の正offset cycleを除いてoffsetを下げられる。

prefix剰余を \(r_i\)、その \(L\) を \(L_i\) とする。最初はactual atomそのものなので \(L_1=1\)。次の文字をatom \(g\) とすると、prefix最小性により \(b_i=b_{i-1}+g-m\) であり、
\[
 \omega_{r_{i-1}}+g=b_i+m(L_{i-1}+1)\in\Gamma.
\]
Apéry最小性から \(L_i\le L_{i-1}+1\)。さらに \(r_i\) がatom剰余なら \(\omega_{r_i}\) 自体がatomであり、上の正の二項の和と等しくなれない。従ってこの場合は \(L_i\le L_{i-1}\)。

よって \(L_\rho-1\) は、その経路が通る非atom非零剰余の個数以下である。それは高々 \(\delta\)。また \(\rho=\rho_k\) へ至るprefixはすべて \(b\le b_{\rho_k}\) の最初の \(k\) 頂点に含まれ、少なくとも最初の頂点はatom剰余なので、高々 \(k-1\) 個である。これで (3.1) が従う。□

\(v_\rho(q)=\operatorname{ord}(\omega_\rho+qm)\) とすれば
\[
 v_\rho(q+1)\ge v_\rho(q)+1,\qquad
 v_\rho(q)=L_\rho+q\quad(q\ge l_\rho-L_\rho).
\]
最小offset語に \(m\) を加えた表示が右辺を実現し、それより長い表示はさらに小さいoffsetを与えてしまうからである。この安定化は各剰余での有限停止も証明する。増分の余剰を足せば
\[
 \sum_{\tau\text{ in residue }\rho}(d(\tau)-1)=L_\rho-s_\rho. \tag{3.2}
\]

経路補題を足して
\[
 \sum_{\rho\ne0}(L_\rho-1)
 \le\sum_{k=1}^{m-1}\min(\delta,k-1)
 =\delta\left(e+\frac\delta2-\frac32\right). \tag{3.3}
\]
以下 \(\mathcal V=e+\delta/2-3/2\)、\(M=m-1\) と書く。この \(\mathcal V\) は幅とは別の数値資源である。すべての議論は数値半群の中で行われ、体や標数に依存しない。

## 4 一つの線形cutを固定する

ここから \(e\ge3\) とする。
\(p(a)=\max\{p:\binom{p+1}{2}\le a\}\) とし、

\[
 r=\max(2,p(a))
\]

と置く。独立な非x一次形式 \(E=(\lambda_1,\ldots,\lambda_r)\) を選んで
\((A/EA)_{\ge2}=0\) とできる。

証明はGreenの次数2の超平面制限定理を反復する。\(a=\binom{p+1}{2}+b\)、\(0\le b\le p\) と書くと、\(s\) 本の一般形式で切った次数2の次元は

\[
 \binom{p+1-s}{2}+\max(b-s,0)\quad(0\le s\le p)
\]

以下であり、\(s=p\) で0となる。標準次数付きなので、それより高い次数も0となる。\(p<2\) なら2本へ拡張する。\(a\le\binom e2\) より \(p(a)\le e-1\) であり、実際のcutは存在する範囲の大きさを持つ。

有限体上では、先に無限な純超越拡大を取り、その体上で一般形式を選ぶ。最終的なintrinsic Betti数は体拡大で変わらないので、最後に元の体へ戻る。異なる標数のrankを等しいとする議論ではない。

\(P=k[\lambda_1,\ldots,\lambda_r]\) を固定する。第2節のイデアル・strataは \(S_0\) 全体に関して定義されているので、\(P\) へ制限しても完全列と作用の一致は保たれる。

## 5 実際の塔と一つの資源列

\(\delta=0\) なら \(\nu=1\)、jump上界から \(N=T=0\)、\(X_2=A_{\ge2}=0\) である。この場合、以下の塔の和はすべて空和とする。

\(F_d\subset N\) をjump \(\le d\) のheadの張るイデアルとし、\(F_1=0\)、\(F_\nu=N\) とする。

\[
 U_s=A/F_{s-1},\quad X_s=(U_s)_{\ge s},\quad
 M_s=(U_s)_{\ge s+1},\quad K_s=F_s/F_{s-1}.
\]

\(U_s\) は次数 \(s\) まで \(Q\) と一致する。square-zero cutにより、すべての \(U_s\) は \(P\) 上次数0、1で生成される。したがって \(X_s\)、\(M_s\) はそれぞれ次数 \(s\)、\(s+1\) のみで極小生成され、

\[
 0\longrightarrow K_s\longrightarrow M_s\longrightarrow X_{s+1}
 \longrightarrow0\quad(2\le s\le\nu),\qquad X_{\nu+1}=0
 \tag{5.1}
\]

は実際の \(P\)-加群完全列である。

\[
 h_{s,t}=\dim(X_s)_{s+t},\qquad H_t=\sum_{s=2}^\nu h_{s,t},
 \qquad S=\sum_{t\ge0}H_t.
\]

これらは有限台を持つ。同じsource・同じ体・同じcutから作った一列である。

剰余 \(\rho\) のApéry座標は、\(H_t\) に区間
\([0,s_\rho-2]\) で1ずつ寄与する。次数 \(p\) のterminalのjumpを \(d\) とすると、そのsuccessor headは区間 \([p,p+d-2]\) で1ずつ寄与する。同じ剰余の次のterminal次数は少なくとも \(p+d\) なので、これらの区間は互いに素である。零剰余には寄与がない。

従って

\[
 H_0=\delta,\qquad 0\le H_t\le M,\qquad
 S=\sum_{\rho\ne0}(L_\rho-1)\le\delta \mathcal V. \tag{5.2}
\]

総和の等式には (3.2) を使う。各剰余でApéryの \(s_\rho-1\) とterminalの \(L_\rho-s_\rho\) が合計 \(L_\rho-1\) となる。

さらに、次数1のterminalの個数を \(\ell\) とすると

\[
 H_1=\delta-a+\ell\le M-a,\qquad H_1\le r\delta.
 \tag{5.3}
\]

最初の等式は、次数3以上のApéry座標が \(\delta-a\) 個、terminal区間が \(t=1\) を含むのは \(p=1\) の場合のみ、という正確な数え上げである。\(\ell\le e-1\) から第一上界を得る。第二上界は、次数 \(s\) の \(q_s\) 個から、\(r\) 本の一次形式で次数 \(s+1\) を生成することから従う。

特に \(r\ge4\) のとき、選んだcutでは \(r=p(a)\) なので

\[
 a_r:=\binom{r+1}{2}\le a\le\delta,
 \qquad H_1\le M-a_r. \tag{5.4}
\]

以下ではこの追加上界を保持する。

## 6 Harmonic評価をKoszul行列から直接証明する

\(P=k[x_1,\ldots,x_r]\)、\(Z\) を次数 \(b\) のみで極小生成される有限長加群、\(h_t=\dim Z_{b+t}\) とする。\(c_j(Z)=\sum_{i=0}^j(-1)^{j-i}\dim\operatorname{Tor}_i^P(Z,k)\) に対し、
\[
 c_j(Z)\le\binom{r-1}{j}\sum_{t\ge0}\frac{j}{t+j}h_t
 \quad(1\le j<r). \tag{H}
\]

**証明。** shiftして \(b=0\) とし、\(P^q\twoheadrightarrow Z\) の斉次核を \(K\) とする。加群単項式順序を固定し、各次数の \(K_d\) をGaussian消去する。pivotでない標準単項式は \(Z_d\) の基底をなし、非標準単項式のnormal formはそれより小さい標準単項式だけで表される。初項加群による商は
\[
 Z^*=P^q/\operatorname{in}K=\bigoplus_{a=1}^qP/I_a
\]
という同shiftの単項式環の直和で、Hilbert関数は同じである。

内部次数を固定し、Koszul基底 \(m e_a\otimes e_F\) を加群単項式ラベル \(x_Fm e_a\) の順に並べる。実際の境界はラベルを上げず、ラベルが同じ部分は \(Z^*\) の多重次数別境界そのものである。各対角blockの最大rank小行列を選んで結合すると、block三角小行列の行列式は対角小行列式の積になる。したがって各内部次数で
\[
 \operatorname{rank}\partial_i(Z)\ge\operatorname{rank}\partial_i(Z^*).
\]
これは元の体上の有限線形代数であり、平坦族定理や一般座標を必要としない。ゆえに単項式商 \(P/I\) について下界を示せば十分である。

次数 \(t\) の標準単項式集合を \(D_t\) とする。
\(\partial_{j+1}:Z_{t-1}\otimes\bigwedge^{j+1}k^r\to Z_t\otimes\bigwedge^jk^r\)
を多重次数 \(\alpha\)、\(|\alpha|=t+j\) ごとに分ける。target行は \((m,F)\)、\(|F|=j\)、\(m=\alpha-\mathbf1_F\in D_t\) である。

\(v\in\operatorname{supp}\alpha\) を固定する。\(v\notin F\) の各target行に対し、source列 \((m/x_v,F\cup\{v\})\) は存在する。標準単項式の約数も標準だからである。この列の他のtarget行はすべて \(v\) を含む。従って選んだ行・列の部分行列は対角 \(\pm1\) であり、
\[
 R_\alpha\ge\#\{(m,F):v\notin F\}.
\]
\(v\) に有理数重み \(\alpha_v/(t+j)\) を付けて平均し、全 \(\alpha\) を足す。\(v\notin F\) では \(\alpha_v=m_v\) なので
\[
 \begin{aligned}
 \operatorname{rank}\partial_{j+1}
 &\ge\frac1{t+j}\sum_{m\in D_t}\sum_{|F|=j}\sum_{v\notin F}m_v\\
 &=\binom{r-1}{j}\frac{t}{t+j}|D_t|.
 \end{aligned} \tag{6.1}
\]
最後は、各 \(v\) を避ける \(j\)-集合が \(\binom{r-1}{j}\) 個、\(\sum_vm_v=t\) を使った。\(t=0\) では右辺0でよい。

\(\ell=\operatorname{length}Z\)、\(R_i\) を全Koszul境界rankとすれば
\[
 b_i(Z)=\binom ri\ell-R_i-R_{i+1},\qquad
 c_j(Z)=\binom{r-1}{j}\ell-R_{j+1}.
\]
(6.1) を \(t\) について足すと (H) を得る。\(\pm1\) は任意標数で非零であり、分数は数値的な重みにすぎない。□

有限長と単一次数生成という仮定は、それぞれ総和の有限性と同shiftの表示に使用した。

## 7 塔から同じcutの全rankへ

完全列 \(0\to K\to M\to L\to0\) の実際のTor connecting rankを \(d_i\) とすると

\[
 b_i(M)=b_i(K)+b_i(L)-d_i-d_{i+1},
 \quad c_j(M)=c_j(K)+c_j(L)-d_{j+1}.
\]

従って \(c_j(M)\le c_j(K)+c_j(L)\)、かつ
\(c_j(K)\le c_j(M)+c_{j+1}(L)\) である。

一方、\(x\) を先に取るKoszulスペクトル系列の実際の \(d_2\)-rankを \(\rho_i\) と書けば、\(k[x,E]\) 上のgeneric ranksは

\[
 c_j(G)=c_j^P(A)+c_{j-1}^P(T)-\rho_{j+1}. \tag{7.1}
\]

以後左辺の \(c_j(G)\) は常にこの \(r+1\) 変数環上の値を表す。
低次数商は

\[
 A/X_2\simeq P/P_+^2\ \oplus\ k(-1)^{e-r-1},\qquad
 L_j=(e-1)\binom{r-1}{j}-\binom{r-1}{j+1}.
\]

第2節の共通strata、(5.1)、(7.1)を合わせると

\[
 \begin{aligned}
 c_1(G)&\le L_1+\sum_s c_1(X_s)+\sum_s\mu_P(M_s),\\
 c_j(G)&\le L_j+\sum_s c_j(X_s)+\sum_s c_{j-1}(M_s)
 \quad(2\le j\le r).
 \end{aligned} \tag{7.2}
\]

すべての省いたconnecting rankは非負の**減算**である。

\(\sum_s\mu_P(M_s)=H_1\) を正確に保ち、(H)を適用すると

\[
 c_j(G)\le L_j+\sum_{t\ge0}W_j(t)H_t. \tag{7.3}
\]

第一rankの重みは

\[
 W_1(0)=r-1,\quad W_1(1)=\frac{r+1}{2},\quad
 W_1(t)=\frac{r-1}{t+1}\ (t\ge2).
\]

\(2\le j\le r\) では

\[
 W_j(0)=\binom{r-1}{j},\quad
 W_j(t)=\frac{j\binom{r-1}{j}}{t+j}
       +\frac{(j-1)\binom{r-1}{j-1}}{t+j-2}\quad(t\ge1).
\]

\(j=r\) も、有限長加群の \(c_r=0\) によって同じ式で扱える。

## 8 実際のordinary targetへ移す

この節では実際のcompletionがordinaryであると仮定する。そのBetti多項式は

\[
 T_m(z)=1+\sum_{i\ge1}i\binom m{i+1}z^i.
\]

\(E\) を非x一次空間の基底へ拡張し、残る \(f=e-r-1\) 本を \(Z\) とする。\(x,E\) を先に取るKoszul二重複体を使う。第0 homologyは実際の平方零代数 \(G/(x,E)G\) であり、その \(k[Z]\) 上の正のBetti数は \(i\binom{f+1}{i+1}\) である。それより高いhomologyは、\(Z\)-Koszul鎖群の次元で評価する。

\(G\) は \(k[x,E]\) 上有限、rank 0、極小生成元数 \(e-r\) なので、その相対Betti多項式は
\((1+z)\sum_{j=0}^r c_j(G)z^j\)、\(c_0=e-r\) となる。これらを代入すると、係数ごとに

\[
 \mathcal B_G(z)\preceq T_{e-r+1}(z)
       +(1+z)^{e-r}\sum_{j=1}^r c_j(G)z^j. \tag{8.1}
\]

一方、\(T_{v+1}-T_v=vz(1+z)^{v-1}\) をtelescopingすれば、十分条件は

\[
 c_j(G)\le R_j,
 \quad R_j=(e-r+j)\binom{\delta+r-1}{j}
              +j\binom{\delta+r-1}{j+1},\quad1\le j\le r.
 \tag{8.2}
\]

この比較は、商のBetti単調性やスペクトル系列の退化を仮定しない。

必要なtarget余裕を、すべての \(j\) について明示する。

\[
 \begin{aligned}
 R_j-L_j
 &=\mathcal V\left[\binom{\delta+r-1}{j}-\binom{r-1}{j}\right]+\Gamma_j,\\
 \Gamma_j
 &=\delta\binom{r-1}{j-1}
 +\frac12\sum_{u=2}^j
 \left[3\binom{r-1}{j-u}+(u-2)\binom r{j-u+1}\right]\binom\delta u
 +\frac{j-1}{2}\binom\delta{j+1}.
 \end{aligned} \tag{8.3}
\]

これはVandermonde展開で得られる恒等式である。全係数が非負であり、Pascalから

\[
 \binom{\delta+r-1}{j}-\binom{r-1}{j}
 =\sum_{v=1}^\delta\binom{r-2+v}{j-1}
 \ge\delta\binom{r-1}{j-1}.
\]

従って、ここでの \(\mathcal V\ge0\) に対し

\[
 R_j-L_j\ge\delta(\mathcal V+1)\binom{r-1}{j-1}. \tag{8.4}
\]

## 9 二本と三本のcutをすべて処理する

\(r=2\) では \(H_1\le S-\delta\) と重みの最大値から
\[
 c_1(G)-L_1\le\tfrac32S-\tfrac12\delta.
\]
また \(H_1\le2\delta\) を使えば
\[
 c_1(G)-L_1\le\tfrac52\delta+\tfrac12S.
\]
\(S\le\delta \mathcal V\) とし、前者は \(\mathcal V\le3\)、後者は \(\mathcal V\ge3\) で \(\delta(\mathcal V+1)\) 以下となる。従ってすべての \(\mathcal V\) で第一rankが払える。top rankも
\[
 c_2(G)\le\sum_{t\ge1}H_t/t\le S-\delta\le\delta(\mathcal V-1)
\]
であり、第8節から払える。\(\delta=0\) は空塔で同じ式に含まれる。

\(r=3\) なら \(a\ge6\)、\(\delta\ge6\)、\(H_1\le M-6\) である。同じ重みから
\[
 \begin{aligned}
 c_1(G)-L_1&\le\tfrac43\delta+\tfrac43H_1+\tfrac23S,\\
 c_2(G)-L_2&\le3\delta+\tfrac32S,\\
 c_3(G)&\le S-\delta.
 \end{aligned}
\]
第一rankのtarget余裕との差は
\[
 \delta(\mathcal V+1)-[\tfrac43\delta+\tfrac43(M-6)+\tfrac23\delta \mathcal V]
 =\frac{\delta(\mathcal V-1)-4(M-6)}3\ge0.
\]
実際、\(z=\delta-6\ge0\) と書けば分子は
\((z+2)e+\binom z2+7>0\)。第二rankは \(\mathcal V\ge2\) から \(2\delta(\mathcal V+1)\) 以下、top rankも払える。実際の3本cutには \(e\ge4\)、\(\delta\ge6\) が必要なので \(\mathcal V\ge11/2>2\) である。

従ってordinary targetを持つ3・4生成元sourceはすべてこの節で閉じる。

## 10 四本以上の全rankを一つの数へ還元する

\(r\ge4\) とし、

\[
 F_r=(r-1)\delta+\frac{r+1}{2}H_1
                 +\sum_{t\ge2}\frac{r-1}{t+1}H_t.
\]

\(2\le j\le r\) について、\(t\ge1\) の重みを \(\binom{r-1}{j-1}\) で割ると

\[
 \frac{r-j}{t+j}+\frac{j-1}{t+j-2}.
\]

\(j\ge3\) では各分母が \(t+1\) 以上なので \((r-1)/(t+1)\) 以下となる。\(j=2\) では、この値と \((r-1)/(t+1)\) の差が

\[
 \frac{2-(r-3)t}{t(t+1)(t+2)}
\]

である。\(t\ge2\) では非正であり、\(t=1\) の場合も \(W_1(1)\) の追加係数1で払える。\(t=0\) では \((r-j)/j\le r-1\) である。

従って **top rankを含めて**

\[
 c_j(G)\le L_j+\binom{r-1}{j-1}F_r\quad(1\le j\le r).
 \tag{10.1}
\]

(8.4) により、同じ一列について

\[
 F_r\le\delta(\mathcal V+1) \tag{10.2}
\]

を証明すればよい。

## 11 固定cutoffによるscalar評価

全ての整数
\[
 e\ge10,\qquad r\ge4,\qquad \delta\ge a_r:=\frac{r(r+1)}2
 \tag{S1}
\]
について、第5節の同じ資源列に対する第10節の scalar は狭義の不等式
\(F_r<\delta(\mathcal V+1)\) を満たす。以下、これを実際のcutの各 \(r\) に直接適用できる形で証明する。

### 11.1 固定cutoffと重み付き上界

\(a=a_r\)、\(d=\delta\) と書き、
\[
 \begin{gathered}
 M=e+d-1,\qquad \mathcal V=e+\frac d2-\frac32,\qquad
 D=D_r=\left\lfloor\frac a2\right\rfloor+1,\qquad
 \mathcal H_D=\sum_{u=1}^D\frac1u,\\
 \alpha=\frac{r-1}{D+1},\qquad c=\frac{r+1}2-\alpha.
 \end{gathered}
 \tag{S2}
\]
と置く。\(a/2=r(r+1)/4\ge r\) なので \(D\ge r\)、従って \(0<\alpha<1\)、\(c>0\) である。\(D\) は以後 \(d\) によらず固定する。

第5節から用いる条件と、第10節の scalar は
\[
 \begin{gathered}
 H_0=d,\qquad H_t\ge0,\qquad \sum_{t\ge0}H_t\le d\mathcal V,\qquad
 H_t\le M,\qquad H_1\le M-a,\\
 F_r=(r-1)d+\frac{r+1}2H_1+
       \sum_{t\ge2}\frac{r-1}{t+1}H_t.
 \end{gathered}
 \tag{S3}
\]
である。重み \(\alpha\) を引くと正確に
\[
 F_r=\alpha\sum_{t\ge0}H_t+(r-1-\alpha)H_0+cH_1
       +\sum_{t\ge2}\left(\frac{r-1}{t+1}-\alpha\right)H_t.
 \tag{S4}
\]
最後の係数は \(t\ge D\) で非正、\(2\le t<D\) で正である。従って (S3) を各項に適用すると
\[
 \begin{aligned}
 F_r\le U_r(e,d;D):={}&\alpha d\mathcal V+(r-1-\alpha)d+c(M-a)\\
 &+M\sum_{t=2}^{D-1}\left(\frac{r-1}{t+1}-\alpha\right).
 \end{aligned}
 \tag{S5}
\]
これは \(H_1\) の容量を一度だけ用いた評価であり、\(H_t\) の台が \(D\) 未満に収まるという仮定を要しない。有限和を足せば
\[
 \begin{gathered}
 U_r(e,d;D)=M+(r-1)K_D-ca,\\
 K_D=d+\frac{d(\mathcal V-1)}{D+1}
       +M\left(\mathcal H_D-2+\frac2{D+1}\right).
 \end{gathered}
 \tag{S6}
\]
差とその \(e\) の係数を
\[
 \begin{gathered}
 G_r(e,d;D)=d(\mathcal V+1)-U_r(e,d;D),\\
 A_r(d;D)=d-1-(r-1)\left(\mathcal H_D-2+\frac{d+2}{D+1}\right)
 \end{gathered}
 \tag{S7}
\]
と置く。(S6) より \(G_r\) は \(e\) の一次式で、
\[
 G_r(e,d;D)=G_r(10,d;D)+(e-10)A_r(d;D).
 \tag{S8}
\]
従って右辺の二つの係数の正性を示せばよい。

### 11.2 三角数基点と六つの小rank

\(e=10,d=a\) では \(M=a+9\)、\(\mathcal V=(a+17)/2\) であり、(S6)–(S7) を整理すると
\[
 \begin{gathered}
 g_0:=G_r(10,a;D)=(r-1)(a+9)(T_r-\mathcal H_D),\\
 T_r=\frac{a(a+22-r)}{2(r-1)(a+9)}+\frac{2r-3}{r-1}
      -\frac{a(a+21)+36}{2(D+1)(a+9)}.
 \end{gathered}
 \tag{S9}
\]
まず
\[
 \mathcal H_{23}=\frac{444316699}{118982864},\qquad
 \frac{747}{200}-\mathcal H_{23}
   =\frac{2107451}{2974571600}>0.
 \tag{S10}
\]
\(D\le23\) なら、\(k=23-D>0\) に対して
\((\sum_{u=D+1}^{23}1/u)(\sum_{u=D+1}^{23}u)\ge k^2\) かつ
\(\sum_{u=D+1}^{23}u=k(D+24)/2\) なので
\[
 \sum_{u=D+1}^{23}\frac1u\ge\frac{2(23-D)}{D+24},\qquad
 \mathcal H_D<\frac{747}{200}-\frac{2(23-D)}{D+24}.
 \tag{S11}
\]
\(k=0\) でも第一式は両辺0であり、第二式は (S10) から従う。次表の最終列は全て正である。

| \(r\) | \(D_r\) | \(T_r\) | \(T_r-747/200+2(23-D_r)/(D_r+24)\) |
|---:|---:|---:|---:|
| 4 | 6 | \(1126/399\) | \(17587/79800\) |
| 5 | 8 | \(35/12\) | \(143/1200\) |
| 6 | 11 | \(623/200\) | \(23/350\) |
| 7 | 15 | \(745/222\) | \(2993/96200\) |
| 8 | 19 | \(622/175\) | \(321/60200\) |
| 9 | 23 | \(269/72\) | \(1/900\) |

従って (S9)–(S11) により \(4\le r\le9\) で \(g_0>0\) である。

### 11.3 単純な障壁による全rankの基点正性

\(\varepsilon=a-2\lfloor a/2\rfloor\in\{0,1\}\) とし、
\[
 \begin{gathered}
 T_\varepsilon(r)=\frac{a(a+22-r)}{2(r-1)(a+9)}+\frac{2r-3}{r-1}
       -\frac{a(a+21)+36}{(a+4-\varepsilon)(a+9)},\\
 B(r)=\frac r4+1+\frac9{2r}.
 \end{gathered}
 \tag{S12}
\]
と置く。\(2(D+1)=a+4-\varepsilon\) なので \(T_r=T_\varepsilon(r)\) であり、引く項の分子は正だから
\(T_1(r)\le T_r\le T_0(r)\) である。通分による恒等式
\[
 \begin{aligned}
 T_1(r)-B(r)
 &=\frac{N(r)}{2r(r-1)(r^2+r+6)(r^2+r+18)},\\
 N(r)&=2r^5-5r^4-148r^3+111r^2-900r+972\\
 &=r^3\bigl((r-10)(2r+15)+2\bigr)
       +r\bigl(111(r-10)+210\bigr)+972
 \end{aligned}
 \tag{S13}
\]
の分母と最終行は \(r\ge10\) で正である。従って \(B(r)<T_1(r)\le T_r\)。

次に \(\mathcal H_{D_r}<B(r)\) を示す。凸関数 \(x\mapsto1/x\) は区間の両端を結ぶ線分以下であるから、連続する \(b\) 個の整数 \(p,\ldots,q\) に対し
\[
 \sum_{u=p}^q\frac1u\le\frac b2\left(\frac1p+\frac1q\right),
 \qquad b=q-p+1.
 \tag{S14}
\]
\(b=1\) のときは等号である。\(r=10\) では \(a=55,D_{10}=28\) なので
\[
 \begin{gathered}
 \mathcal H_{28}-\mathcal H_{23}
 \le\frac52\left(\frac1{24}+\frac1{28}\right)=\frac{65}{336},\\
 B(10)-\frac{747}{200}-\frac{65}{336}
 =\frac{79}{20}-\frac{747}{200}-\frac{65}{336}
 =\frac{181}{8400}>0.
 \end{gathered}
 \tag{S15}
\]
(S10) と合わせ \(\mathcal H_{28}<B(10)\) を得る。

一般に \(a_{r+1}=a_r+r+1\) より、\(b=D_{r+1}-D_r\) は
\[
 b\le\frac{r+2}2,\qquad D_r+1\ge\frac{a_r+3}2,\qquad
 D_{r+1}\ge\frac{a_{r+1}+1}2.
 \tag{S16}
\]
従って (S14) から
\[
 \begin{aligned}
 \mathcal H_{D_{r+1}}-\mathcal H_{D_r}
 &\le\frac b2\left(\frac1{D_r+1}+\frac1{D_{r+1}}\right)\\
 &\le\frac{r+2}2\left(\frac1{a_r+3}+\frac1{a_{r+1}+1}\right)
 <\frac2r.
 \end{aligned}
 \tag{S17}
\]
最後の狭義不等式は
\[
 \frac2r-\frac{r+2}2\left(\frac1{a_r+3}+\frac1{a_{r+1}+1}\right)
 =\frac{8(r^2+3r+6)}{r(r^2+r+6)(r^2+3r+4)}>0
 \tag{S18}
\]
による。一方、\(r\ge10\) なら
\[
 B(r+1)-B(r)-\frac2r
 =\frac{r^2-7r-26}{4r(r+1)}
 =\frac{(r-10)(r+3)+4}{4r(r+1)}>0.
 \tag{S19}
\]
(S15)、(S17)、(S19) による帰納で \(r\ge10\) の全域に
\(\mathcal H_{D_r}<B(r)<T_r\) が従う。六つの小rankと (S9) を合わせて
\[
 g_0=G_r(10,a;D)>0\qquad(r\ge4)
 \tag{S20}
\]
を得た。

### 11.4 固定cutoffの正二次式と全域の正性

\(A_0=A_r(a;D)\) と置く。(S6)–(S7) の基点での恒等式は
\[
 \begin{gathered}
 g_0=(a+9)A_0+C,\\
 C=\frac{a[-a(D-r+2)-D(r-4)+3]}{2(D+1)}<0.
 \end{gathered}
 \tag{S21}
\]
実際、\(D\ge r\)、\(a\ge10\)、\(r\ge4\) により分子の括弧は高々 \(-2a+3<0\) である。(S20)–(S21) より
\[
 A_0>\frac{-C}{a+9}>0.
 \tag{S22}
\]
さらに
\[
 b_0=A_0+11-r-8\alpha
 \tag{S23}
\]
の正性を評価する。\(\eta\in\{0,1\}\) に対し
\[
 \begin{gathered}
 D_\eta=\frac{a-\eta}2+1,\qquad
 C_\eta=\frac{a[-a(D_\eta-r+2)-D_\eta(r-4)+3]}{2(D_\eta+1)},\\
 F_\eta=\frac{-C_\eta}{a+9}+11-r-\frac{8(r-1)}{D_\eta+1}
 \end{gathered}
 \tag{S24}
\]
と定義する。実際の偶奇 \(\varepsilon\) について \(C_\varepsilon=C\) なので (S22) から \(b_0>F_\varepsilon\)。通分すれば
\[
 \begin{gathered}
 F_0-F_1=\frac{(r-1)(a^2+17a+144)}{(a+3)(a+4)(a+9)}>0,\\
 F_1=\frac a2-\frac{3r}2+\frac{11}2
       +\frac{3(5r+31)}{2(a+9)}-\frac{17(r-1)}{a+3}.
 \end{gathered}
 \tag{S25}
\]
ここで \(r\ge4\) より
\[
 \begin{gathered}
 \frac a2-\frac{3r}2+\frac{11}2
 =\frac{r^2-5r+22}4
 =\frac92+\frac{(r-1)(r-4)}4\ge\frac92,\\
 a+3-4(r-1)=\frac{(r-3)(r-4)}2+1>0.
 \end{gathered}
 \tag{S26}
\]
従って (S25) の正の項を落とし、\((r-1)/(a+3)<1/4\) を使うと
\[
 b_0>F_\varepsilon\ge F_1>\frac92-\frac{17}4=\frac14.
 \tag{S27}
\]

\(D\) を固定したまま (S6)–(S7) を差し引くと
\[
 \begin{gathered}
 A_r(d+1;D)-A_r(d;D)=1-\alpha,\\
 G_r(10,d+1;D)-G_r(10,d;D)
    =A_r(d;D)+11-r-8\alpha.
 \end{gathered}
 \tag{S28}
\]
従って任意の整数 \(t=d-a\ge0\) に対して、一次式とその有限和は正確に
\[
 A_r(a+t;D)=A_0+t(1-\alpha)>0,
 \tag{S29}
\]
\[
 G_r(10,a+t;D)=g_0+t b_0+(1-\alpha)\binom t2>0.
 \tag{S30}
\]
となる。\(g_0>0\)、\(b_0>1/4\)、\(1-\alpha>0\) であり、\(t\) は非負整数なので \(\binom t2=t(t-1)/2\ge0\) である。最後に (S8)、(S29)–(S30) から
\[
 G_r(e,d;D)>0,\qquad F_r\le U_r(e,d;D)<d(\mathcal V+1)
 \quad(e\ge10,\ r\ge4,\ d\ge a_r).
 \tag{S31}
\]
第10節の十分条件が、実際のcutの全ての \(r\ge4\) で成立する。これにより同節の全ての相対rank、従って第8節の移行後の全てのordinary rankの比較が得られる。

## 12 共通端点模型とactual接錐への移行

### 12.1 仮定、整数コア、最大分解長

本節では体 \(k\) を任意とし、整数
\[
q\ge2,\quad 0<a_1<\cdots<a_q<u<m,\quad d\ge1,
\quad \gcd(a_1,\ldots,a_q,u)=\gcd(m,d)=1
\tag{E1}
\]
に対して
\(\Gamma=\langle m,m+da_1,\ldots,m+da_q,m+du\rangle\)、
\(G=\operatorname{gr}_{\mathfrak m}k[[t^\Gamma]]\) と置く。
これらの生成元は最小である。実際、offset \(a\le u\) の生成元に長さ \(l\ge2\)、offset 和 \(B\) の表示があれば、
\((l-1)m=d(a-B)\) から \(l-1=jd\)、\(a-B=jm\ge m>u\) となり矛盾する。生成元全体の最大公約数は1なので \(\Gamma\) は数値半群である。本節で必要な幅条件は \(u<m\) であり、\(du<m\) は仮定しない。

\(h\in\Gamma\) の最大分解長を \(\nu(h)\) とする。生成元が正なのでこの最大値は有限であり、\(G_n\) の基底は \(\nu(h)=n\) を満たす \((t^h)^*\) である。異なる数値指数の間に一次関係はない。

以下の環と、その変数の像を同じ文字で表す。
\[
\begin{gathered}
S=k[x,y_1,\ldots,y_q,v],\qquad E=k[x,v],\qquad
T=k[y_1,\ldots,y_q],\\
C=k[s,st^{a_1},\ldots,st^{a_q},st^u],\qquad
x=s,\quad y_j=st^{a_j},\quad v=st^u.
\end{gathered}
\]
\(C\) の生成元の次数は1とする。その単項式は次数・offset の対 \((n,B)\)、すなわち \(s^nt^B\) で区別される。写像
\[
\phi:C\twoheadrightarrow G,\qquad
s^nt^B\longmapsto (t^{nm+dB})^*\in G_n
\quad\bigl(\nu(nm+dB)>n\text{ なら }0\bigr)
\tag{E2}
\]
は次数付き環全射である。全射性は各 \(h\) の最大長表示から従う。固定した \(n\) では異なる \(B\) は異なる \(nm+dB\) を与えるため、\(\ker\phi\) は \(C\) の単項式基底の一部で張られる単項式イデアルである。生存条件は常に \(\nu(nm+dB)=n\) である。

### 12.2 有限な端点座標模型

\(0\le r<u\)、\(\epsilon_r=[r>0]\) とする。コア単項式には一意な座標
\[
B=r+uK,\qquad n=L+K+\epsilon_r,\qquad L,K\ge0
\tag{E3}
\]
がある。\(L\ge0\) は \(B\le nu\) による。\(x\) は \(L\) を、\(v\) は \(K\) を1増やす。

\(\alpha=(\alpha_1,\ldots,\alpha_q)\in\mathbb N^q\)、\(|\alpha|\le u-1\) について
\[
B_\alpha=\sum_j\alpha_ja_j,\quad
r=B_\alpha\bmod u,\quad
K=\lfloor B_\alpha/u\rfloor,\quad
L=|\alpha|-K-\epsilon_r
\tag{E4}
\]
を作り、同じ \(r\) の \(x^Lv^K\) で生成する \(E\) の単項式イデアルを \(M_r\) とする。この有限リストで全コアを生成できる。内部因子が \(u\) 個以上ある語の最初の \(u\) 因子を取り、空語を含む \(u+1\) 個の prefix offset を mod \(u\) で見ると二つが一致する。その間の非空語は長さ \(l\)、offset \(cu\) を持ち、\(0<a_j<u\) より \(1\le c\le l-1\) である。この語を \(x^{l-c}v^c\) に換えると内部因子数が減る。反復すれば内部因子数は \(u-1\) 以下になる。

また gcd 条件から内部ステップは \(\mathbb Z/u\) 全体を生成する。有限群では負のステップも同じステップの非負回数に換えられるので、全剰余に内部語で達する。最短経路は頂点を重複しないため長さ \(u-1\) 以下である。従って全 \(M_r\ne0\)、\(M_0=E\) であり、\(E\) 加群として
\[
C\simeq\bigoplus_{r=0}^{u-1}M_r[\epsilon_r,r],\qquad
H_x:=\max_{r,(L,K)\in\operatorname{Min}M_r}L\le u-2.
\tag{E5}
\]
ここで \(\operatorname{Min}\) は座標ごとの順序の極小点、添字の括弧は (E3) の次数・offset の移動を表す。\(r\ne0\) の極小点は (E4) のリストから選べるので \(L+K\le u-2\) であり、\(r=0\) の極小点は \((0,0)\) だけである。この直和は \(E\) 加群の直和である。

### 12.3 長い表示との競合とactual核

\((n,B)\) と同じ数値指数に長さ \(n+\delta\) の表示があることは
\(\delta m=d(B-B')\) と同値である。従って gcd 条件から、長い表示との競合は正確に
\[
(n,B)\longmapsto(n+jd,B-jm),\qquad j\ge1
\tag{E6}
\]
で尽くされる。

長い側の剰余を \(r\)、短い側の剰余を \(s\) とし、\(r+jm=s+cu\) と書く。長い側の極小点 \((L,K)\in\operatorname{Min}M_r\) から生じる短い側の競合領域は、次の点の上方閉集合である。
\[
\left(\max\{0,L-jd-c+\epsilon_r-\epsilon_s\},\ K+c\right).
\tag{E7}
\]
実際、clamp 前の短い側の座標は
\((L-jd-c+\epsilon_r-\epsilon_s,K+c)\) である。長い側を極小点の上方へ動かし、短い側にも非負条件を課すと、第一座標だけを0で切った (E7) が得られる。切断後の第一座標0は、長い側の第一座標を増やすことで実現する。\(m>u\) より \(c\ge1\) なので第二座標の切断は不要である。

全 \(j\ge1\) と全 \(\operatorname{Min}M_r\) からの (E7) で生成するイデアルを \(T_s\subset E\) とする。短い側がコアに属する条件を合わせると、actual核とactual接錐は
\[
N_s=M_s\cap T_s,\qquad
G\simeq\bigoplus_{s=0}^{u-1}M_s/N_s[\epsilon_s,s]
\tag{E8}
\]
となる。特に \(N_s\) は一般には \(T_s\) 自体ではない。

### 12.4 全競合の有限停止と端点rank

\(jm=hu+t\)、\(0\le t<u\) と書いて剰余の繰上がりを調べると
\[
c-\epsilon_r+\epsilon_s\ge\lfloor jm/u\rfloor,
\qquad
\max\{0,L-jd-c+\epsilon_r-\epsilon_s\}
\le\max\{0,H_x-2j\}.
\tag{E9}
\]
最初の不等式は、\(t=0\) なら \(s=r,c=h\)、\(t>0\) なら \(r+t<u\)、\(r+t=u\)、\(r+t>u\) の三場合から従う。後半では \(d\ge1\)、\(\lfloor jm/u\rfloor\ge j\) を用いた。

\(J_0=\lfloor(u-2)/2\rfloor\)、\(p=u/\gcd(m,u)\) と置く。\(j>J_0\) なら (E7) の第一座標は全て0である。短い側 \(s\) を固定して \(j\) を \(j+p\) へ増やすと、長い側の剰余 \(r\) は同じで、\(c\) は \(m/\gcd(m,u)\) 増える。第一座標0の範囲では後の生成元は前の倍数になる。従って、\(T_{s,j}\) を固定した \(j\) からの生成イデアルとすれば
\[
T_s=\sum_{j=1}^{J_0+p}T_{s,j},\qquad N_s=M_s\cap T_s.
\tag{E10}
\]
さらに \(D_0=d+\lfloor m/u\rfloor\) とすれば、\(J_0\) を
\(\max\{0,\lfloor(H_x-1)/D_0\rfloor\}\) に換えてもよい。いずれも全ての \(m,d\) に対する停止式である。

全剰余の \(M_r\) は非零なので、各 \(T_s\) は大きな \(j\) から純粋な \(v\) 冪を含む。また数値指数の等式
\(m(m+du)=(m+du)m\) の右辺はより長い表示を与えるため
\[
v^m=0\text{ in }G,\qquad v^mM_s\subset N_s,
\qquad \operatorname{rank}_E G=0.
\tag{E11}
\]
\(G\) は (E5) の商なので有限生成 \(E\) 加群である。

### 12.5 コア商と端点Koszul homology

\[
Q_C=C/(x,v)C,\quad P_C=\dim_kQ_C,\qquad
Q_G=G/(x,v)G,\quad P_G=\dim_kQ_G,\qquad
R=\dim_k(0:_G(x,v))
\tag{E12}
\]
と置く。\(Q_C\) は標準次数付き \(T\) の Artin 商であり、基底はちょうど全 \(\operatorname{Min}M_r\) である。prefix 消去から \((Q_C)_n=0\) for \(n\ge u\) でもある。

actual商の極小 \(E\) 生成元は、生存する \(M_s\) の極小点に一致する。従って
\[
\begin{aligned}
P_C&=\sum_s\#\operatorname{Min}M_s,\\
P_G&=\sum_s\#\{g\in\operatorname{Min}M_s:g\notin N_s\},\\
R&=\sum_s\#\{(L,K)\in M_s\setminus N_s:
 (L+1,K),(L,K+1)\in N_s\}.
\end{aligned}
\tag{E13}
\]
最後の数も有限に計算できる。\(N_s\) の極小点を
\((A_0,B_0),\ldots,(A_t,B_t)\)、\(A_0<\cdots<A_t\)、\(B_0>\cdots>B_t\) と並べると、\(E/N_s\) の両端点socle基底は正確に
\[
(A_{i+1}-1,B_i-1),\qquad 0\le i<t
\tag{E14}
\]
である。各候補は \(x,v\) のいずれを掛けても隣接生成元に入り、逆に両方で殺される点はこの隣接角に限られる。このうち \(M_s\) に属する点が (E13) の \(R\) に寄与する。\(E/N_s\) が Artin である必要はない。

端点Koszul複体 \(K(x,v;G)\) の第0、第2 homology の次元は \(P_G,R\) である。有限生成 \(E\) 加群の最小自由解消は長さ2以下であり、(E11) と分数体上のEuler恒等式から第1 homologyの次元も定まる。従って
\[
\boxed{\dim_kH_\bullet(x,v;G)=(P_G,P_G+R,R).}
\tag{E15}
\]

### 12.6 \(m,d\) に一様な \(P_C,R\) の評価

内部ステップによる mod \(u\) の最短語長を \(\ell_r\)、\(\ell_0=0\) とし、最短語の点を \((L_r,K_r)\) とする。
\[
W=1+\sum_{r=0}^{u-1}\ell_r,\qquad
L_r+K_r=\ell_r-\epsilon_r,
\qquad P_C\le W.
\tag{E16}
\]
最後の不等式を示す。最短点は \(M_r\) の極小点である。支配する別の点があれば座標和が減り、より短い内部語が存在するためである。\(r\ne0\) の極小点を第一座標昇順に並べると、最短点の左には高々 \(L_r\) 個、右には高々 \(K_r\) 個ある。従って極小点数は \(L_r+K_r+1=\ell_r\) 以下である。\(M_0=E\) の1点を加えれば (E16) を得る。

次に \(T_s\) の極小点を第一座標昇順に並べ、その数を \(z_s+1\)、最後の第二座標、すなわち最小第二座標を \(\kappa_s\) とする。純粋な \(v\) 冪があるので最初の第一座標は0である。任意の \((A,B)\in T_s\) を割る極小点を取ると、その左の点数はその第一座標以下、右の点数はその第二座標と \(\kappa_s\) の差以下なので
\[
z_s\le A+B-\kappa_s\quad((A,B)\in T_s),\qquad
\kappa_s\ge\left\lceil\frac{m-s}{u}\right\rceil,
\quad \sum_{s=0}^{u-1}\left\lceil\frac{m-s}{u}\right\rceil=m.
\tag{E17}
\]
\(\kappa_s\) の下界は各競合生成元の第二座標 \(K+c\) と
\(c=(r+jm-s)/u\ge(m-s)/u\) による。

各最短点に \(j=1\) の競合を適用する。\(s=(r+m)\bmod u\) は剰余の置換であり、そのcarry \(c_r\) の総和は \(m\) である。(E7) の第一座標は \(L_r\) 以下なので、(E17) を足すと
\(\sum_s z_s\le\sum_r(L_r+K_r)=W-u\) を得る。
自然な単射 \(M_s/(M_s\cap T_s)\hookrightarrow E/T_s\) はsocleにも単射を誘導し、後者のsocle次元は (E14) と同じ角の計数から \(z_s\) である。従って \(R\le W-u\)。さらに (E9) より \(T_s\) の全極小点の第一座標は \(\max(H_x-2,0)\) 以下で、相異なる整数であり、0も含む。以上から
\[
\boxed{P_C\le W,\qquad
R\le\widehat R:=\min\{W-u,\ u\max(H_x-2,0)\}.}
\tag{E18}
\]
この評価は \(\gcd(m,u)=1\) や Cohen–Macaulay 性を必要としない。

### 12.7 actual核を保持したBetti移行

\(b_i^T(-)=\dim_k\operatorname{Tor}_i^T(-,k)\)、
\(\beta_i(G)=\dim_k\operatorname{Tor}_i^S(G,k)\) とし、範囲外の二項係数と負の添字のBetti数を0とする。\(Q_C\twoheadrightarrow Q_G\) の実際の核を \(K\) とすると \(\dim_kK=P_C-P_G\) である。Tor長完全列と \(K\) のKoszul鎖群の次元から
\[
b_i^T(Q_G)\le b_i^T(Q_C)+b_{i-1}^T(K)
\le b_i^T(Q_C)+(P_C-P_G)\binom q{i-1}.
\tag{E19}
\]

actual \(G\) 上の端点・内部Koszul二重複体を用い、端点homologyを先に取る。有限spectral sequenceは \(\operatorname{Tor}^S(G,k)\) に収束する。第0行を正確に \(\operatorname{Tor}^T(Q_G,k)\) とし、他の行を鎖群次元で評価すると、(E15) より
\[
\beta_i(G)\le b_i^T(Q_G)
 +(P_G+R)\binom q{i-1}+R\binom q{i-2}.
\tag{E20}
\]
後続pageは各全次数で部分商になるので次元は増えない。(E19) とPascal恒等式から、共通端点補題の移行式は
\[
\boxed{\beta_i(G)\le b_i^T(Q_C)
 +P_C\binom q{i-1}+R\binom{q+1}{i-1}.}
\tag{E21}
\]
右辺の \(R\) は \(\widehat R\) に換えられる。内部変数は剰余成分を移すが、この二重複体は actual \(G\) 上で定義されている。

### 12.8 二内部変数の場合

\(q=2\)、\(a_1=a,a_2=b\)、\(y_1=y,y_2=z\) とする。このとき \(Q_C\) は \(k[y,z]\) の単項式Artin商である。実際、次数 \(n\) の純内部語 \(y^{n-j}z^j\) のoffsetは \(na+j(b-a)\) で互いに異なる。従って生存する純内部語同士の線形関係はなく、\(T\to Q_C\) の核は単項式で張られる。

socle次元 \(\sigma_C=\dim_k(0:_{Q_C}(y,z))\) も有限整数計数で求まる。一般に基底点 \((r,L,K)\) に内部offset \(a_j\) を掛け、\(r+a_j=s+cu\) と書くと移動先は
\[
\bigl(s,L+1+\epsilon_r-c-\epsilon_s,K+c\bigr).
\tag{E22}
\]
この点が \(M_s\) の極小点ならその基底元へ、極小でなければ0へ写る。固定した乗法の異なる非零像は異なる次数・offsetを持つので、\(\sigma_C\) は (E22) の \(y,z\) がともに0になる基底点数に等しい。これは標数に依存しない。二変数Koszul複体の第0homologyは \(k\)、第2homologyはsocleであり、有限長加群のEuler恒等式から
\[
\bigl(b_0^T(Q_C),b_1^T(Q_C),b_2^T(Q_C)\bigr)
=(1,\sigma_C+1,\sigma_C).
\tag{E23}
\]
従って (E21) は
\[
\boxed{\begin{aligned}
\beta_0(G)&=1,\\
\beta_1(G)&\le P_C+\sigma_C+1+R,\\
\beta_2(G)&\le2P_C+\sigma_C+3R,\\
\beta_3(G)&\le P_C+3R,\\
\beta_4(G)&\le R,\qquad \beta_i(G)=0\quad(i>4).
\end{aligned}}
\tag{E24}
\]
ここでも \(R\) を \(\widehat R\) に換えられる。端点homologyの第0行も鎖群次元で評価すれば、実際の \(P_G,R\) による粗い評価
\((\beta_1,\beta_2,\beta_3,\beta_4)
\le(3P_G+R,3P_G+3R,P_G+3R,R)\) も得られる。

### 12.9 Artin商の親子計数と全行評価

\(A=T/I\) を \(I_1=0\) の標準次数付きArtin商とし、\(h_n=\dim_kA_n\)、\(P=\sum_nh_n\) とする。従って \(h_0=1,h_1=q\) である。同次初期イデアル \(J\) を取り、\(B_n\) を次数 \(n\) の標準単項式集合とする。全ての直接約数が \(B_n\) にある次数 \(n+1\) の単項式の集合を \(D_n\) とすると、\(J\) の次数 \(n+1\) の極小生成元数は \(\#D_n-h_{n+1}\) である。

子 \(y^\alpha\) から親 \(y^{\alpha-e_j}\) への重みを \(\alpha_j/(n+1)\) とする。各子の総重みは1であり、各親 \(y^\gamma\) から全候補子への総重みは
\(\sum_j(\gamma_j+1)/(n+1)=(n+q)/(n+1)\) である。従って \(\#D_n\le(n+q)h_n/(n+1)\)。\(I\) は \(J\) の極小単項式生成元に対応する同次Gröbner基底で生成されるから \(b_1^T(A)\le b_1^T(T/J)\)。以上を \(n\) について足すと
\[
\begin{aligned}
b_1^T(A)&\le q+\sum_{n\ge1}\frac{(q-1)h_n}{n+1}\\
&\le\frac{q-1}{3}P+\frac{(q+1)(q+2)}6.
\end{aligned}
\tag{E25}
\]
後半は \(h_1=q\) と \(n\ge2\) での \(1/(n+1)\le1/3\) による。有理重みは整数個数の評価であり、基礎体内の除法ではない。

次数2の情報を保持すれば、同じ計数からさらに
\[
\begin{aligned}
b_1^T(A)&\le\frac{q-1}{4}P+\frac{(q+1)^2}{4}
                  +\frac{q-1}{12}h_2,\\
b_1^T(A)-P&\le q-1+
 \sum_{n\ge1}\frac{q-n-2}{n+1}h_n.
\end{aligned}
\tag{E26}
\]
最初の式は \(n\ge3\) で \(1/(n+1)\le1/4\) として得られる。特に \(q=5\) なら
\[
b_1^T(A)-P\le4+h_1+\frac{h_2}{3}
\le4+5+\frac{\binom62}{3}=14.
\tag{E27}
\]

高次行には、任意標数で
\[
\boxed{b_i^T(A)\le P\binom qi-\binom{q+1}{i+1}
\quad(i\ge1)}
\tag{E28}
\]
を使える。これを直接証明する。Koszul微分の係数次数0から1への部分を考え、各 \(i\) 元集合 \(J_0\subset\{1,\ldots,q\}\) の列に対し行
\((y_{\min J_0},J_0\setminus\{\min J_0\})\) を選ぶ。\(A_1\) で \(y_1,\ldots,y_q\) は独立であり、この行は対応する列だけに係数 \(\pm1\) を持つ。従って整数行列の段階で \(\binom qi\) 次の単位小行列があり、任意体で \(\operatorname{rank}d_i\ge\binom qi\) である。隣接微分についても \(\operatorname{rank}d_{i+1}\ge\binom q{i+1}\) なので、
\(b_i=\dim K_i-\operatorname{rank}d_i-\operatorname{rank}d_{i+1}\) とPascal恒等式から (E28) を得る。\(i>q\) は双方0である。

\(A=Q_C\)、\(P=P_C\) として (E21) に代入すれば、幅側で用いる一様評価は
\[
\boxed{\begin{aligned}
\beta_1(G)&\le P_C+
 \left\lfloor q+\sum_{n\ge1}\frac{(q-1)h_n}{n+1}\right\rfloor
 +\widehat R,\\
\beta_i(G)&\le P_C\binom{q+1}i
 +\widehat R\binom{q+1}{i-1}-\binom{q+1}{i+1}
 \qquad(2\le i\le q+2).
\end{aligned}}
\tag{E29}
\]
第一行には必要に応じて (E26)、(E27) の強い評価も使える。

## 13 五生成元以上の幅側

### 13.1 定理、実際の比較先、共通の端点評価

任意の体 \(k\) 上で
\[
\Gamma=\langle m,m+da_1,\ldots,m+da_q,m+du\rangle,
\quad e=q+2\ge5,\quad 0<a_1<\cdots<a_q<u<m,
\quad d\ge1,
\]
\[
\gcd(m,d)=\gcd(u,a_1,\ldots,a_q)=1
\]
とする。この節では、その接錐 \(G=G_\Gamma\) の全 Betti 数が、実際の区間完備化
\(\widetilde\Gamma=\langle m,m+1,\ldots,m+du\rangle\) の接錐の対応する Betti 数以下であることを証明する。各 Betti 数は、それぞれの最小生成系の多項式環上で取る。

この表示の最小生成性は自動的である。実際、offset \(a\le u\) の生成元が長さ \(l\ge2\)、offset 和 \(B\ge0\) の語なら、
\((l-1)m=d(a-B)\)。互いに素性から \(l-1=jd, a-B=jm\ge m>u\) となり、矛盾する。二つの gcd 条件により半群は数値半群である。

比較先の実効幅は常に
\(V=\min(du,m-1)\ge u\) である。第1.3節の算術列公式から、正の第 \(i\) 行の容量は
\[
 F_i^{\min}(u):=i\binom u{i+1}
       +\min\left\{\binom u{i-1},\binom ui\right\}
 \le \beta_i(G_{\widetilde\Gamma}).                 \tag{W1}
\]
以下、範囲外の二項係数は0とする。この下界は物理幅 \(du\) を正規化幅 \(u\) に取り替えた target ではなく、実効幅 \(V\ge u\) と公式の幅に関する非減少性から得る下界である。

整数コアと端点を
\[
 C=k[s^u,s^{u-a_1}t^{a_1},\ldots,s^{u-a_q}t^{a_q},t^u],
 \quad x=s^u,\quad v=t^u,\quad Q_C=C/(x,v)C,
 \quad T=k[y_1,\ldots,y_q]
\]
と置き、\(b_i(Q_C)=\beta_i^T(Q_C)\)、\(P_C=\dim_kQ_C\) と書く。この表示は第12節のcoreと、次数・offset \((n,B)\) を \(s^{un-B}t^B\) に送る次数付き同型で結ばれる。実際の商は \(Q_G=G/(x,v)G\)、その長さは \(P_G\) であり、\(P_C\) と同一視しない。第12節で証明した、実全射 \(Q_C\twoheadrightarrow Q_G\) の kernel–Tor 補償を含む移行式は
\[
 \beta_i(G)\le b_i(Q_C)+P_C\binom q{i-1}
                         +R\binom{q+1}{i-1},
 \qquad R=\dim_k(0:_G(x,v)).                         \tag{W2}
\]
具体的には核の長さ \(P_C-P_G\) が
\(b_i(Q_G)\le b_i(Q_C)+(P_C-P_G)\binom q{i-1}\)
を与え、端点 Koszul homology の長さが
\((P_G,P_G+R,R)\) であるために (W2) となる。商の Betti 単調性は使わない。

内部 offset の mod \(u\) 最短語長を \(\ell_r\)、\(\ell_0=0\) とし、
\[
 W=1+\sum_{r=0}^{u-1}\ell_r.
\]
第12節の剰余ごとの平面単項式イデアル \(M_r\) の極小点を \((L,K)\)、その第一座標の最大値を \(H_x\) とする。同節の、元の向きの実競合イデアルに対する corner 評価から
\[
 P_C\le W,\qquad
 R\le\widehat R:=\min\{W-u,\ u\max(H_x-2,0)\}.        \tag{W3}
\]
ここで \(R\) は実 source の socle 長である。コアの反射によってこの \(R\) や \(H_x\) を別の向きへ移すことはしない。

また、\(h_n=\dim_k(Q_C)_n\)、\(h_0=1,h_1=q\) に対する第12節の Artin 評価を再掲する：
\[
\begin{aligned}
b_1(Q_C)
&\le q+\sum_{n\ge1}\frac{(q-1)h_n}{n+1}\\
&\le\frac{q-1}{3}P_C+\frac{(q+1)(q+2)}6,\\
b_1(Q_C)
&\le\frac{q-1}{4}P_C+\frac{(q+1)^2}{4}
                   +\frac{q-1}{12}h_2
 \le\frac{q-1}{4}P_C+\frac{(q+1)(q+2)(q+3)}{24},\\
b_i(Q_C)&\le P_C\binom qi-\binom{q+1}{i+1}\quad(i\ge1).
\end{aligned}                                                    \tag{W4}
\]
第二の第一行評価は、incidence 和の \(n\ge3\) の係数を \((q-1)/4\) に緩め、\(h_2\le\binom{q+1}{2}\) としたものである。有理重みは整数の個数を評価するために用い、体内の除法ではない。

### 13.2 最小幅と一欠落幅

まず \(u=q+1=e-1\) は完全な算術列 source である。第1.3節の算術列公式の剰余パラメータを \(1\le c\le u\) とすると、第一項 \(i\binom u{i+1}\) への補正は、\(i\le c\) なら \((c+1-i)\binom u{i-1}\)、\(i>c\) なら \((i-c)\binom ui\) である。前者は
\((u+1-i)\binom u{i-1}=i\binom ui\) 以下、後者も \(i\binom ui\) 以下なので、各正行は \(i\binom{u+1}{i+1}=i\binom e{i+1}\) 以下である。\(V\ge e\) なら (W1) の第一項がこれを払う。\(V=e-1\) なら \(d=1\) または \(m=e\) である。前者は source と完備化が等しい。後者は \(c=u\) の同じ公式から双方の Betti 数が \(i\binom m{i+1}\) に一致する。従って最小幅は全 \(m,d\) で閉じる。

次に一欠落幅 \(u=q+2=e\) を処理する。欠落 offset を \(h\in\{1,\ldots,u-1\}\) と書くと、内部 offset は \(\{1,\ldots,u-1\}\setminus\{h\}\) である。整数コアの基底元を次数・offset \((n,b)\) で記す。\(B=\{0,1,\ldots,u\}\setminus\{h\}\) とすると、次数 \(n\) の基底は
\[
 nB\setminus\bigl((n-1)B\cup((n-1)B+u)\bigr)
\]
である。

内部欠落 \(2\le h\le u-2\) では
\[
 (Q_C)_0=k,\qquad
 (Q_C)_1=\langle y_a:1\le a<u,\ a\ne h\rangle,
\]
\[
 (Q_C)_2=kz_-\oplus kz_+,
 \quad z_-=(2,h),\quad z_+=(2,h+u),\qquad
 (Q_C)_{\ge3}=0.                                      \tag{W5}
\]
実際、\(B\cup(B+u)\) に欠ける候補は \(h,h+u\) だけで、それぞれ
\(1+(h-1)\)、\((u-1)+(h+1)\) で表される。従って \(B+B=[0,2u]\) であり、次次数では
\((B+B)\cup(B+B+u)=[0,3u]\) がすべてを消す。標準次数付き性から全高次数も消える。

端欠落 \(h=1\) では \(B+B=\{0\}\cup[2,2u]\) であり、次次数も
\((B+B)\cup(B+B+u)=\{0\}\cup[2,3u]\) が \(3B\) を含む。従って
\[
 (Q_C)_2=k(2,u+1),\qquad (Q_C)_{\ge3}=0.              \tag{W6}
\]
\(h=u-1\) のコア基底は \((n,b)\mapsto(n,nu-b)\) により \((Q_C)_2=k(2,u-1)\) となる。これはコア基底だけの反射である。元の向きで各基底点を見ても
\(L=n-\lceil b/u\rceil\le1\) なので、すべての場合に \(H_x\le1\)、従って元の source の \(R=0\) を (W3) から得る。欠落剰余だけが最短長2であるため
\[
 W=q+3,\qquad
 P_C=\begin{cases}q+3&2\le h\le u-2,\\q+2&h=1,u-1.\end{cases}
                                                               \tag{W7}
\]

内部欠落では \(E_1=(Q_C)_1=U\oplus Z\) とし、
\[
 U=\langle y_a:a<h\rangle,\quad r=h-1,\qquad
 Z=\langle y_a:a>h\rangle,\quad s=u-h-1,\quad r+s=q.
\]
乗法は
\[
 y_ay_b=\begin{cases}
 z_-&a,b<h,\ a+b=h,\\
 z_+&a,b>h,\ a+b=h+u,\\
 0&\text{それ以外}.
 \end{cases}                                             \tag{W8}
\]
各ブロックのフォームは \(a\mapsto h-a\)、\(a\mapsto h+u-a\) の置換行列である。平方項も係数1であり、標数2でも係数は消えない。

実 Koszul 微分の次数1から2への部分を
\[
 D_i:E_1\otimes\bigwedge^iE_1
       \longrightarrow(kz_-\oplus kz_+)\otimes\bigwedge^{i-1}E_1
\]
とする。各 column \(y_a\otimes e_I\) は、そのフォーム双対が \(I\) にあるとき一つの \(\pm1\)、なければ0を持つ。
行 \(z_-\otimes e_J\) が非零である必要十分条件は \(U\not\subseteq J\) である。実際、\(v_0\in U\setminus J\) を取り、そのフォーム双対を \(v_0^*\) とすれば、column
\(v_0^*\otimes e_{J\cup\{v_0\}}\) はその行だけに \(\pm1\) を持つ。逆に \(U\subseteq J\) なら来る column がない。第二ブロックも同様である。非零行ごとにこの column を選ぶと、元の整数行列に対角 \(\pm1\) 小行列を得る。従って全体で正確に
\[
 \rho_i:=\operatorname{rank}D_i
 =2\binom q{i-1}-\binom s{i-1-r}-\binom r{i-1-s}.     \tag{W9}
\]
零行数が上界を、同じ行列の単位 minor が下界を与えている。

次数0から1への微分は \(\bigwedge^iE_1\to E_1\otimes\bigwedge^{i-1}E_1\) で、各 \(i\) 元集合の最小要素を選ぶ単位 minor により rank は \(\binom qi\) である。異なる内部次数の rank を加えると、\(1\le i\le q\) について
\[
 b_i(Q_C)=(q+2)\binom qi-\binom q{i+1}-\rho_i-\rho_{i+1}.
\]
Pascal 恒等式で整理すれば、範囲外の \(b_i=0\) も含めて全 \(i\ge1\) で
\[
 b_i(Q_C)=i\binom{q+1}{i+1}-2\binom q{i-1}+T_i,
 \qquad T_i=\binom{s+1}{i-r}+\binom{r+1}{i-s}.          \tag{W10}
\]
\(b_0=1\) は別に扱う。

ここで \(r,s\ge1\)、\(q=r+s\ge3\) に対し、二つの包含単射から
\[
 T_i\le\binom{q+2}i,\qquad
 T_i\le\binom{q+2}{i-1}\quad(i\ge1)                  \tag{W11}
\]
が従う。第一の単射を明記する。互いに素な集合 \(U,Z\)（大きさ \(r,s\)）と追加二点 \(a,b\) を取り、第一項の部分集合 \(D\subseteq Z\cup\{a\}\)、\(|D|=i-r\) を \(U\cup D\) に、第二項の \(E\subseteq U\cup\{b\}\)、\(|E|=i-s\) を \(Z\cup E\) に写す。共通像は \(i=q\) の \(U\cup Z\) 一つだけである。この第二コピーを、固定した \(u_0\in U,z_0\in Z\) に対する
\[
 (U\setminus\{u_0\})\cup(Z\setminus\{z_0\})\cup\{a,b\}
\]
へ移す。この像は元のどちらの族にもなく、単射になる。

第二の単射では \(k=q+1-i\) と置く。\(k<0\) なら \(T_i=0\)。\(k\ge0\) では
\(T_i=\binom{r+1}k+\binom{s+1}k\) である。大きさ \(r+1,s+1\) の互いに素な集合 \(A_1,A_2\) に各二点を固定し、一方の \(k\) 元部分集合に反対側の固定二点を加える。二族の衝突は \(k=2\) の四固定点の集合だけである。\(q\ge3\) なので一方に三点あり、その側の三点と他方の一点からなる未使用の像へ第二コピーを移せる。これで \(k+2\) 元集合への単射となり、その個数は \(\binom{q+2}{k+2}=\binom{q+2}{i-1}\) である。

(W2)、(W7)、(W10) と \(R=0\) により
\[
 \beta_i(G)\le i\binom{q+1}{i+1}
                   +(q+1)\binom q{i-1}+T_i.
\]
恒等式 \(i\binom{q+1}i=(q+1)\binom q{i-1}\) を使うと、(W1) とこの上界との差は正確に
\[
 \min\left\{\binom{q+2}{i-1},\binom{q+2}i\right\}-T_i\ge0.
\]

端欠落では全 \(q\) 変数上の置換フォームが一つであり、同じ元行列の単位 minor から
\[
 \rho_i=\binom q{i-1}\quad(1\le i\le q),\qquad \rho_{q+1}=0.
\]
\(P_C=q+2\)、\(R=0\) を (W2) に代入すると、全 \(i\ge1\) で
\[
 \beta_i(G)\le i\binom{q+2}{i+1}
                   +\mathbf1_{i=q}+\mathbf1_{i=q+1}.   \tag{W12}
\]
第 \(q+1\) 行では右辺は \(q+2=P_C\) であり、この指示関数を落としてはいけない。二つの指示関数が現れる行では (W1) の最小補正項は1以上なので、ともに支払われる。以上で一欠落幅の全行を得た。

### 13.3 密な幅：欠落 prefix と一つの lex ideal

欠落数を \(t=u-1-q\) とする。非零コア基底元を表す内部語の長さを \(n\) とする。長さ \(l\ge2\) の部分語の剰余が既存 offset \(a\) なら、その offset 和は \(a+cu\)、\(0\le c\le l-1\) であり、その語は
\(x^{l-c-1}v^cy_a\) に等しい。端点因子を持つので \(Q_C\) では0である。剰余0なら offset 和は \(cu\)、\(1\le c\le l-1\) であり、同様に \(x^{l-c}v^c=0\) となる。

従って長さ2から \(n\) の prefix 剰余はすべて欠落 offset である。二つが同じなら間の非空部分語の剰余が0となる。長さ1の内部語の剰余は0でなく、長さ2以上なら今の議論で消えるので、これも不可能である。よって \(n-1\) 個の異なる欠落が必要であり、
\[
 (Q_C)_n\ne0\Longrightarrow n\le t+1,
 \qquad H_x\le t.
\]
\(0\le t\le q\) なら \(A=\{0,a_1,\ldots,a_q\}\subseteq\mathbb Z/u\mathbb Z\) は \(q+1>u/2\) 元を持つ。任意の剰余 \(r\) に対し \(A\cap(r-A)\ne\varnothing\) なので、すべての剰余は長さ2以下で到達する。既存 \(q\) 剰余は最短長1、欠落 \(t\) 剰余は最短長2である。従って
\[
 W=q+1+2t,\quad P_C\le q+1+2t,\quad R\le t,
 \qquad t\le2\Longrightarrow R=0.                    \tag{W13}
\]
最後の主張は、元の向きの \(H_x\le t\) と (W3) による。

同じ全 Hilbert 関数の lex ideal を \(L\subseteq T\) とする。辞書順は \(y_1>\cdots>y_q\) とし、標準単項式は各次数で辞書順最小の \(h_n\) 個である。そのうち最初の \(j\) 変数だけに支持される個数を \(S_j(n)\) とする。\(S_0(n)=0\)（\(n>0\)）、\(S_q(n)=h_n\)、\(S_j(1)=j\) である。

最大変数が \(y_j\) の次数 \(n\) の極小生成元数を \(g_j(n)\) とする。lex ideal の stability により、shadow 中の最大変数 \(y_j\) の単項式は、前次数の ideal 中の最初の \(j\) 変数だけの単項式と、\(y_j\) の乗除で一対一に対応する。全単項式数を引き算すれば
\[
 g_j(n)=S_j(n-1)-S_j(n)+S_{j-1}(n).
\]
Artin 性により高次数で0なので、次数について telescope すると
\[
 \sum_{n\ge2}g_j(n)=j+\sum_{n\ge2}S_{j-1}(n).
\]
第1節の任意標数の Bigatti–Hulett–Pardue 上界と Eliahou–Kervaire 公式から、すべての行で同じ \(L\) を用いて
\[
\begin{aligned}
b_i(Q_C)&\le i\binom{q+1}{i+1}
       +\sum_{n\ge2}\sum_{j=1}^q S_{j-1}(n)\binom{j-1}{i-1}\\
&\le i\binom{q+1}{i+1}+K\binom{q-1}{i-1},
\qquad K=\sum_{n\ge2}\sum_{j=1}^qS_{j-1}(n).
\end{aligned}                                                   \tag{W14}
\]
第一項には \(\sum_j j\binom{j-1}{i-1}=i\binom{q+1}{i+1}\) を使った。

密な範囲では \(\sum_{n\ge2}h_n=P_C-1-q\le2t\)。\(r\le q\) が \(\binom{r+1}{2}\ge2t\) を満たせば、全 \(n\ge2\) の lex 標準単項式は末尾 \(r\) 変数に支持される。実際、この変数内の次数 \(n\) 単項式は \(\binom{n+r-1}n\ge\binom{r+1}{2}\ge h_n\) 個あり、外の変数を持つものよりすべて辞書順で小さい。

全直接除数がこの次数 \(n\) の標準集合に入る次数 \(n+1\) 単項式を「子」と呼び、その数を \(M_n\) とする。子も同じ末尾 \(r\) 変数に支持される。外の変数が残れば、それを残す直接除数が標準集合の外に出るからである。最大変数 \(y_j\) を除く写像は、子と最初の \(j\) 変数だけに支持される標準単項式を対応させる。逆写像で \(y_j\) を掛けたとき、他の直接除数は元の親より辞書順で小さいので標準である。従って
\[
 M_n=\sum_{j=1}^qS_j(n),\qquad
 M_n-h_n=\sum_{j=1}^qS_{j-1}(n).
\]
親子 incidence に、除く変数の子での指数を重みとして与える。各子への総重みは \(n+1\)、各親からの末尾 \(r\) 変数内の全候補子への総重みは \(n+r\) である。ゆえに
\[
 K\le\sum_{n\ge2}\frac{r-1}{n+1}h_n
       \le\frac{2t(r-1)}3.                            \tag{W15}
\]
この調和評価も整数集合の重み付き計数であり、標数に依存しない。

以下 \(q\ge4\)、\(2\le t\le q\) とする。(W2)、(W13)、(W14) による source 上界は
\[
 i\binom{q+1}{i+1}+K\binom{q-1}{i-1}
       +(q+1+2t)\binom q{i-1}+R\binom{q+1}{i-1}.      \tag{W16}
\]
\(t=2\) は \(r=3\) を選び、整数性から \(K\le\lfloor8/3\rfloor=2\)、また \(R=0\) である。target の第一項の Vandermonde 展開により、その容量と (W16) の差は
\[
 (q-3)\binom q{i-1}+i\binom{q+1}{i-1}
                         -2\binom{q-1}{i-1}\ge0.
\]
二つの正項がそれぞれ一つの \(\binom{q-1}{i-1}\) を払う。\(t=3\) でも \(r=3\) として \(K\le4\)、\(R\le3\)。最初の二つの非負増分を残せば差は
\[
 (2q-4)\binom q{i-1}+(3i-3)\binom{q+1}{i-1}
                         -4\binom{q-1}{i-1}\ge0.
\]
\(q\ge4\)、\(i\ge1\) から従う。

\(4\le t\le q\) では \(\binom{t+1}{2}\ge2t\) なので \(r=t\)、\(K\le2t(t-1)/3\) とする。Vandermonde 展開から
\[
 i\binom{q+t+1}{i+1}-i\binom{q+1}{i+1}
 \ge t(q+1)\binom q{i-1}+i\binom t2\binom{q+1}{i-1}.
\]
\(R\le t\)、\(i\binom t2-t\ge t(t-3)/2\ge0\) を使い、二項係数を比較すると差は
\[
 \left[\frac{5t^2-17t-6}{6}+(t-1)(q-t)\right]\binom q{i-1}
\]
以上である。\(t=4+z\)、\(q=t+v\)、\(z,v\ge0\) とすれば括弧の6倍は
\(5z^2+23z+6+6zv+18v>0\)。これで \(q\ge4\) の密な全幅
\(q+1\le u\le2q+1=2e-3\) が閉じた。\(t=0,1\) は13.2で既に処理した。

### 13.4 疎な幅：Kneser 評価と全高次行

まず \(a=e-1\)、\(s=\lceil a/2\rceil=\lfloor e/2\rfloor\) と置く。巡回群の集合 \(A=\{0,a_1,\ldots,a_q\}\) は \(a\) 元を持ち、全群を生成する。第1節の Kneser の和集合定理を
\[
 |X+Y|\ge|X+H|+|Y+H|-|H|,
 \qquad H=\operatorname{Stab}(X+Y)
\]
の形で使う。\((n+1)A\) が真部分集合なら \(H\) は真部分群である。\(A+H\) が \(c\) 個の \(H\)-coset を含むとき、\(A\) は群を生成し0を含むので \(c\ge2\)、かつ \(c|H|\ge a\)。従って
\[
 |(n+1)A|\ge|nA|+(c-1)|H|\ge|nA|+\lceil a/2\rceil.
\]
最後は \((c-1)|H|\ge c|H|/2\ge a/2\) と整数性による。したがって、合成数 \(u\) も含めて
\[
 |nA|\ge\min\{u,a+(n-1)s\}\quad(n\ge1).
\]
\(0\in A\) なので \(nA\) は長さ高々 \(n\) の到達集合である。最短長を層ごとに数えると
\[
 W=u+\sum_{n\ge1}(u-|nA|)
 \le B(u):=u+\sum_{j\ge0}(u-a-sj)_+.                  \tag{W17}
\]

\(\Delta=u-a=sk+b\)、\(0\le b<s\) と書けば
\[
\begin{aligned}
B(u)&=u+\frac{\Delta^2}{2s}+\frac\Delta2
                         +\frac{b(s-b)}{2s}\\
&\le B_*(u):=u+\frac{\Delta^2}{2s}+\frac\Delta2
                         +\frac{\lfloor s^2/4\rfloor}{2s},
\qquad B(u)\le\frac{u^2}{e-1}.
\end{aligned}                                                   \tag{W18}
\]
最後の不等式は、差の \(2a\) 倍が
\[
 2a\left(\frac{u^2}{a}-B(u)\right)
 =s(2s-a)k^2+ask+2(2s-a)kb+2b^2\ge0
\]
となることによる。

ここから \(e\ge6\)、\(u\ge2e-2\) とする。(W2)–(W4)、\(P_C\le B\)、\(R\le B-u\) より
\[
\begin{aligned}
\beta_1(G)&\le\frac{e+3}{3}B-u+\frac{e(e-1)}6,\\
\beta_1(G)&\le\frac{e+5}{4}B-u+\frac{(e-1)e(e+1)}{24},\\
\beta_i(G)&\le U_i:=B\binom ei-u\binom{e-1}{i-1}
                                      -\binom{e-1}{i+1}
                         \quad(2\le i\le e).
\end{aligned}                                                   \tag{W19}
\]

第一行について、\(e=6,7,8,9\) では第二の上界と \(B\le B_*\) を使う。
\[
 z=u-(2e-2)\ge0,\qquad
 D_*:=\binom u2+1-
 \left[\frac{e+5}{4}B_*-u+\frac{(e-1)e(e+1)}{24}\right]
\]
に対する正確な恒等式は次の通りである。

| \(e\) | \(B_*(u)\) | \(D_*\)、\(u=2e-2+z\) |
|---|---|---|
| 6 | \((u^2-u+12)/6\) | \(z^2/24+43z/24+1/2\) |
| 7 | \((u^2-3u+20)/6\) | \(2z+1\) |
| 8 | \((u^2-2u+25)/8\) | \(3z^2/32+63z/16+211/32\) |
| 9 | \((u^2-4u+36)/8\) | \(z^2/16+17z/4+29/4\) |

全係数が非負で定数項が正なので、四つの全無限範囲で第一行が閉じる。これは offset の列挙ではない。\(e\ge10\) は第一の上界と \(B\le u^2/(e-1)\) だけでよく、同じ \(z\) に対して
\[
\begin{aligned}
&\binom u2+1-
 \left[\frac{e+3}{3(e-1)}u^2-u+\frac{e(e-1)}6\right]\\
&\qquad=\frac{(e-1)(e-10)}2+1
          +\frac{4e-33}{6}z+\frac{e-9}{6(e-1)}z^2>0.
\end{aligned}                                                   \tag{W20}
\]
これで疎な全 \(e\ge6\) の第一行が閉じた。

高次行では (W19) の最後の上界を使う。\(e\ge8\) の第二行は
\[
 2\binom u3-U_2
 \ge\frac u6[2u^2-(3e+6)u+6e-2]+\binom{e-1}3.
\]
\(e=8+v\)、\(u=2e-2+z\) と置くと中括弧は
\(2v^2+5vz+16v+2z^2+26z+18>0\) である。\(e=6\)、\(u\ge10\) は同じ粗い \(B\le u^2/5\) から
\[
 2\binom u3-U_2\ge (u-10)(u-3)(u+1)/3\ge0.
\]
\(e=7\)、\(u=12+z\) は一般の中括弧が
\(2z^2+21z+4>0\) となる。従って第二行は全 \(e\ge6\) で閉じる。

第二行から第 \(e\) 行まで一度に移すため、\(2\le i\le e\) について
\[
 \mathcal T_i(u)=\frac{i\binom u{i+1}}{\binom ei}
       +\frac{ui}{e}
       +\frac{(e-i)(e-i-1)}{e(i+1)}                    \tag{W21}
\]
と置く。
\(i\binom u{i+1}\ge U_i\) はちょうど \(\mathcal T_i(u)\ge B(u)\) と同値である。基点では
\(\mathcal T_i(e)=e-1+i/e\) であり、幅を1増す差は
\[
 \mathcal T_i(u+1)-\mathcal T_i(u)
      =i\frac{\binom ui}{\binom ei}+\frac ie.
\]
\(u\ge e\) で \(\binom ui/\binom ei\) は \(i\) について非減少である。実際、隣接比は \((u-i)/(e-i)\ge1\)（\(i<e\)）。従って基点も各増分も \(i\) とともに増え、\(\mathcal T_i(u)\ge\mathcal T_2(u)\ge B(u)\)。これで上端 \(i=e\) を含む全高次行が閉じる。

### 13.5 五生成元の残る幅

以下 \(q=3,e=5\)。\(u=4\) は最小幅、\(u=5\) は一欠落幅なので13.2による。

まず任意の三変数 Artin 商 \(Q_C\) について、(W4) から
\[
 b_1\le6+\sum_{n\ge2}\frac{2h_n}{n+1}\le P_C+2.
\]
次数0の単位元は \(h_1=3\) により socle でないので \(b_3\le P_C-1\)。三変数多項式環上の rank-zero Euler 特性から
\(b_2=b_1+b_3-1\le2P_C\)。これを (W2) に代入すると
\[
 (\beta_2,\beta_3,\beta_4,\beta_5)
 \le(5P_C+4R,\ 4P_C+6R-1,\ P_C+4R,\ R).             \tag{W22}
\]

\(u=6\)、\(t=2\) では (W13) より \(P_C\le8,R=0\)。incidence 評価の整数性から
\[
 b_1\le\left\lfloor\frac{2P_C}{3}+\frac{10}{3}\right\rfloor
 \le8,\qquad \beta_1\le P_C+b_1\le16=\binom62+1.
\]
\(u=7\)、\(t=3\) では \(P_C\le10,R\le3\) であり、常に \(b_1\le10\)。\(R=0\) なら \(\beta_1\le20\)。\(R>0\) なら (W3) より \(H_x\ge3\) である。剰余0の唯一の極小点は \((0,0)\) であり、非零剰余の点の次数は \(L+K+1\) なので、このとき \((Q_C)_4\ne0\)。特に \(\tau=\sum_{n\ge3}h_n\ge1\) である。従って
\[
 b_1\le6+\frac23(P_C-4)-\frac16\tau
          \le10-\frac16<10,
\]
すなわち整数性から \(b_1\le9\)。よってこの場合も
\(\beta_1\le10+9+3=22=\binom72+1\)。この \(b_1\le9\) は \(R>0\) の場合にだけ用いた。

残る行は (W22) と次の容量比較で閉じる。

| \(u\) | \((P_C,R)\) の上界 | 第2–5行の上界 | \((F_2^{\min},F_3^{\min},F_4^{\min},F_5^{\min})\) |
|---|---|---|---|
| 6 | \((8,0)\) | \((40,31,8,0)\) | \((46,60,39,11)\) |
| 7 | \((10,3)\) | \((62,57,22,3)\) | \((77,126,119,56)\) |

次に \(u\ge8\) とする。四元集合 \(A=\{0,a,b,c\}\subseteq\mathbb Z/u\mathbb Z\) に Kneser を適用する。\((n+1)A\) が真部分集合で、その stabilizer の位数が \(h\)、\(A+H\) の coset 数が \(c_0\) なら、増分は少なくとも \((c_0-1)h\)。\(c_0\ge2\)、\(c_0h\ge4\) なので、これが3未満となるのは \(h=c_0=2\) だけである。このとき \(A\) 自体が二つの \(H\)-coset の全体であり、
\[
 u=2h',\qquad A=\{0,t,h',t+h'\},\quad
 0<t<h',\quad\gcd(t,h')=1.                           \tag{W23}
\]
最後の互いに素性は \(A\) が全巡回群を生成することによる。これを antipodal の場合と呼ぶ。それ以外では全段階の増分が3以上なので
\[
 |nA|\ge\min(u,3n+1),\qquad
 W\le B_3(u):=u+\sum_{j\ge0}(u-4-3j)_+.
\]
剰余別に和を取れば
\[
\begin{aligned}
B_3(3j)&=(3j^2+j+2)/2,\\
B_3(3j+1)&=(3j^2+3j+2)/2,\\
B_3(3j+2)&=(3j^2+5j+4)/2.
\end{aligned}                                                   \tag{W24}
\]
(W4) の第二の第一行評価はここでは \(b_1\le P_C/2+5\) である。(W2)、(W3) により非 antipodal の第一行は
\[
 \beta_1\le\left\lfloor\frac52B_3(u)-u+5\right\rfloor.
\]
容量 \(\binom u2+1\) と床を取る前の右辺との差は、\(u=3j,3j+1,3j+2\) の順に
\[
 \frac{3j^2+j-26}{4},\qquad
 \frac{3j^2+3j-22}{4},\qquad
 \frac{3j^2+5j-24}{4}.
\]
\(u\ge9\) では各該当 \(j\ge3\) で正である。\(u=8\) は \(B_3(8)=13\) から
\(\beta_1\le\lfloor65/2-8+5\rfloor=29=\binom82+1\) となる。

antipodal の場合は \(u=2h\)、\(h\ge4\) と書き直し、offset \(t,h,t+h\) の変数を \(y,z,w\) とする。このとき整数コアを直接記述すると
\[
 Q_C=k[y,z,w]/(yz,z^2,zw,(y,w)^h).                    \tag{W25}
\]
実際、最初の三積はそれぞれ端点を含む表示を持つ。\((y,w)\) の次数 \(n<h\) の単項式は offset \(nt+jh\)、\(0\le j\le n\) を持つ。\(\gcd(t,h)=1\) により異なる次数 \(0\le n<h\) の剰余 mod \(h\) は異なるので、これらは端点因子を持つ短い表示に入らず、同一次数の offset も相異なる。次数 \(h\) では offset は \((t+j)h\)。\(t+j\) が偶数なら両端点だけ、奇数なら \(z\) と両端点で長さ \(h\) に表せるので全て消える。これで (W25) の全基底が尽くされる。

従って
\[
 P_C=\binom{h+1}{2}+1,\qquad b_1(Q_C)=h+4,
 \qquad W=h^2-h+2.
\]
最後は、mod \(h\) の各非零剰余が唯一の \(1\le n<h\) に対応し、その上の二剰余はともに最短長 \(n\)、残る剰余 \(h\) は最短長1であることによる。(W2) と \(R\le W-2h\) を使うと、第一行容量と上界の差は
\[
 \binom{2h}{2}+1-[P_C+(h+4)+W-2h]
      =\frac{h^2+h-12}{2}\ge0.
\]

最後に \(u\ge8\) の全高次行を、二つの構造の場合で共通に払う。一般の (W18) を \(e=5\) に適用すると
\(P_C\le W\le u^2/4\)、\(R\le u^2/4-u\)。従って (W22) の第二行上界と target の第一項との差は
\[
 2\binom u3-\left(\frac{9u^2}{4}-4u\right)
       =\frac{u(4u-7)(u-8)}{12}\ge0.
\]
残る三行については、さらに粗く
\[
 (\beta_3,\beta_4,\beta_5)
      \le\left(\frac52u^2,\frac54u^2,\frac14u^2\right).
\]
\(u=8\) で target の第一項 \((3\binom84,4\binom85,5\binom86)=(210,224,140)\) はこの上界 \((160,80,16)\) より大きい。固定 \(k\ge3\) について \(\binom uk/u^2\) は \(u\ge k\) で増加する。隣接比の比較は
\(u^2-(u+1)(u+1-k)=(k-2)u+k-1>0\) に等しい。従って \(k=4,5,6\) の三比較は全 \(u\ge8\) で保たれ、第5行まで閉じる。

以上、\(e\ge6\) は13.2–13.4で密な範囲 \(u\le2e-3\) と隣接する疎な範囲 \(u\ge2e-2\) を、\(e=5\) は13.2と13.5で全 \(u\ge4\) を覆う。第0行は双方1、\(i>e\) では source の Koszul homology は0である。全議論は任意体で成立し、有限 offset core の計算を使わず、全 \(d\ge1\)、全 \(m>u\)、全行について実際の区間完備化への比較を得た。□

## 14 四生成元の真正狭幅

### 14.1 主張と共通端点評価

任意体 \(k\) 上で、次の全パラメータを考える。
\[
\Gamma=\langle m,m+da,m+db,m+du\rangle,
\quad0<a<b<u,\quad\gcd(a,b,u)=\gcd(m,d)=1,
\quad d\ge1,\quad m\ge du+2,\quad V=du.
\tag{N1}
\]
\(G=\operatorname{gr}_{\mathfrak m}k[[t^\Gamma]]\) とする。本節は全 \(i\) について
\(\beta_i(G)\le F_i(m,V)\) を証明する。\(F_i\) は §1 の**物理幅 \(V\)** の
実区間完備化の公式であり、正規化幅 \(u\) と取り違えない。
公刊入力は §1 の Kneser 定理、Savchev–Chen の unit 定理、任意体での区間 target 公式である。
有限部分は後述する196個の offset 対の厳密整数計算だけである。

正規化された斉次環とその端点商を
\[
C=k[s,st^a,st^b,st^u],\quad Q_C=C/(x,v)C,
\quad P_C=\dim_k Q_C,\quad\sigma_C=\dim_k(0:_{Q_C}(y,z))
\tag{N2}
\]
と書く。\(x,y,z,v\) の offset は順に \(0,a,b,u\) である。
\(D\subset\mathbb N^2\) を、同じ次数・offset に端点を含む表示を持たない内部語
\(y^sz^t\) の集合とする。同じ次数・offset の二つの内部語は
\(s+t=s'+t',\ as+bt=as'+bt'\) から一致する。従って \(Q_C\) は二変数の単項式
Artin 商であり、\(D\) はその単項式基底である。特に \(D\) は divisor に閉じる。

\(\ell_r\) を \(\mathbb Z/u\mathbb Z\) でステップ \(a,b\) を用いる最短語長
（\(\ell_0=0\)）とし、\(W=1+\sum_r\ell_r\) と置く。また
\[
H_x=\max_{(s,t)\in D}\left\{s+t-\left\lfloor\frac{as+bt}{u}\right\rfloor
 -\boldsymbol1_{(as+bt)\bmod u>0}\right\},\qquad R=\dim_k(0:_G(x,v)).
\tag{N3}
\]
§12 の共通端点補題と、実 kernel の補償を保持した二内部変数の Koszul 評価は
\[
P_C\le W,\qquad R\le\widehat R:=\min\{W-u,\ u\max(H_x-2,0)\},
\tag{N4}
\]
\[
\begin{aligned}
\beta_1(G)&\le P_C+\sigma_C+1+R,&
\beta_2(G)&\le2P_C+\sigma_C+3R,\\
\beta_3(G)&\le P_C+3R,&\beta_4(G)&\le R.
\end{aligned}
\tag{N5}
\]
これらは (N1) の全 \(m,d\) に適用される。以下では実接錐の Betti 数を直接この式で評価する。

### 14.2 巡回三点集合の距離和と二変数 socle

\(A=\{0,a,b\}\subset\mathbb Z/u\mathbb Z\) とする。全 \(n\ge0\) に対し
\[
|nA|\ge\min\{u,2n+1\}.
\tag{N6}
\]
\(n=0\) は明らか。\(n\ge1\) で \(nA\) が全群なら成立する。それ以外ではその stabilizer を
\(H\) とする。Kneser の反復形により
\[
|nA|\ge n|A+H|-(n-1)|H|.
\tag{N7}
\]
実際、\(H\) による商では \(n\bar A\) は非周期的であり、\(j\bar A\) の stabilizer は
\(n\bar A\) のそれに含まれるので \(1\le j\le n\) の各段も非周期的である。
二集合 Kneser を反復して \(|n\bar A|\ge n|\bar A|-(n-1)\) を得れば (N7) となる。
\(|H|=1\) なら右辺は \(2n+1\)。\(|H|\ge2\) なら \(H\) は真部分群であり、
\(A\subset H\) は \(\gcd(a,b,u)=1\) に反する。\(0\in A\) なので
\(|A+H|\ge2|H|\)、従って右辺は \((n+1)|H|\ge2n+2\) である。
これで合成数 \(u\) と非自明 stabilizer も含めて (N6) が従う。

0 で語を補えるので \(nA=\{r:\ell_r\le n\}\)。非負整数の尾和公式から
\[
W=1+\sum_{n\ge0}(u-|nA|)
\le1+\sum_{n\ge0}\max(u-2n-1,0)
=1+\left\lfloor\frac{u^2}{4}\right\rfloor.
\tag{N8}
\]
有限 downset の socle が \(s\) 個あるとき、その極大点を第一座標昇順に
\((\alpha_i,\beta_i)\), \(0\le i<s\) と並べると、第二座標は厳密に減少する。
従って \(\alpha_i\ge i,\ \beta_i\ge s-1-i\)。全ての次数 \(s-1\) の単項式
\(y^iz^{s-1-i}\) とその全 divisor が downset に属する。よって
\[
\binom{\sigma_C+1}{2}\le P_C\le W\le1+\left\lfloor u^2/4\right\rfloor,
\qquad\sigma_C\le u-1.
\tag{N9}
\]
最後は \(u\ge3\) で \(\binom{u+1}{2}>1+u^2/4\) だからである。

### 14.3 標準語の純軸と混合部分

まず純 \(y\) 語の長さは \(u-2\) 以下である。
\(g=\gcd(a,u)>1\) なら \(q=u/g\le u-1\) として
\(y^q=x^{q-a/g}v^{a/g}\) だから \(y^q\) は標準でない。
\(g=1\) なら \(qa\equiv b\pmod u\) を満たす一意な \(q\in\{2,\ldots,u-1\}\) がある。
\(qa=b+ku\) と書けば \(-u<qa-b<qu\) から \(0\le k\le q-1\) であり、
\[
y^q=x^{q-1-k}zv^k
\tag{N10}
\]
の右辺には合計 \(q-1>0\) 個の端点がある。従って標準な純 \(y\) 冪は高々 \(u-2\) 乗。
\(a,b\) を交換すれば純 \(z\) 軸も同じである。

次に \((s,t)\in D\), \(s,t>0\) とし、\(s\) 個の \(a\) と \(t\) 個の \(b\) を巡回群の列とみなす。
非空零和部分列の長さが \(e\)、整数和が \(Ku\) なら \(1\le K\le e-1\) であり、
対応因子を \(x^{e-K}v^K\) に替えて端点表示ができる。従ってこの列は零和を持たない。
\(s+t>u/2\) と仮定し、§1 の Savchev–Chen の unit 定理を適用する。
unit 倍後の二種類の正代表値が双方2以上なら総和は \(2(s+t)>u\) となるので、一方は1、
他方は \(c\ge2\) である。元の offset をそれぞれ \(\alpha,\beta\)、個数を \(R_0,T_0\ge1\) と書く。
\(c\alpha\equiv\beta\pmod u\) なので \(c\alpha=\beta+ku\) と書け、
\(-u<c\alpha-\beta<cu\) から \(0\le k\le c-1\)。従って
\[
Y_\alpha^c=x^{c-1-k}Y_\beta v^k.
\tag{N11}
\]
右辺の端点個数は \(c-1>0\) なので \(R_0<c\)。定理の総和条件は
\(R_0+cT_0\le u-1\) であるから
\[
2(R_0+T_0)=(R_0+cT_0)+(R_0-(c-2)T_0)
\le(u-1)+(c-1-(c-2))=u,
\tag{N12}
\]
仮定に反する。\(h=\lfloor u/2\rfloor\) とすれば、以上より
\[
st>0\Longrightarrow s+t\le h,\qquad
s+t\le u-2\ ((s,t)\in D),\qquad
P_C\le B_{\rm cap}:=\binom h2+2u-3.
\tag{N13}
\]
最後は混合語が高々 \(\binom h2\) 個、二軸が単位元を一度数えて高々 \(2u-3\) 個だからである。
また非空語では \(\lceil(as+bt)/u\rceil\ge1\) なので (N3) から
\(H_x\le\max(u-3,0)\)。特に \(u=3,4\) では (N4) により \(R=0\) である。

### 14.4 高次行を全幅で比較する

(N4)、(N5)、(N8)、(N9) を代入して
\[
\begin{aligned}
\beta_2(G)&\le5W-2u-1\le5u^2/4-2u+4=:U_2(u),\\
\beta_3(G)&\le4W-3u\le u^2-3u+4=:U_3(u),\\
\beta_4(G)&\le W-u\le u^2/4-u+1=:U_4(u).
\end{aligned}
\tag{N14}
\]
§1 の実 target 公式は次の下界を与える。
\[
\begin{aligned}
L_1(V)&=\binom V2+1\le F_1(m,V),\\
L_2(V)&=2\binom V3+V\le F_2(m,V)&& (V\ge3),\\
L_3(V)&=3\binom V4+\binom V2\le F_3(m,V)&& (V\ge5),\\
L_4(V)&=4\binom V5\le F_4(m,V).
\end{aligned}
\tag{N15}
\]
例えば第2行の補正項は \(D\ge2\) なら \((D-1)V\ge V\)、\(D=1\) なら
\(\binom V2\ge V\)。第3行は \(D\ge3\) なら \((D-2)\binom V2\)、
\(D=2,1\) ならそれぞれ \(\binom V3,2\binom V3\) であり、\(V\ge5\) ではいずれも
\(\binom V2\) 以上となる。これらの明示下界は \(V\) に関して非減少なので \(V=du\ge u\) を使える。

第2行は \(u=6+z\), \(z\ge0\) に対し
\[
12\{L_2(u)-U_2(u)\}=4z^3+45z^2+152z+108>0.
\tag{N16}
\]
\(u=5\) は床を保持して \(W\le7,\ R\le2,\ \sigma_C\le4\) より
\(\beta_2(G)\le24<25=L_2(5)\)。第3・4行は \(u=5+z\), \(z\ge0\) で
\[
8\{L_3(u)-U_3(u)\}=z^4+14z^3+67z^2+134z+88>0,
\tag{N17}
\]
\[
60\{L_4(u)-U_4(u)\}=2z^5+30z^4+170z^3+435z^2+458z+105>0.
\tag{N18}
\]
\(u=4\) は \(R=0,\ P_C\le5\) と (N9) から \(\sigma_C\le2\) なので
\((\beta_2,\beta_3,\beta_4)\le(12,5,0)\)。\(V=4\) の実 target 最小値は第2行12、第3行7であり、
\(V\ge5\) は (N15) が支払う。\(u=3\) は \((a,b)=(1,2)\) のみで、
\(Q_C=k[y,z]/(y,z)^2\)、従って \((P_C,\sigma_C,R)=(3,2,0)\)。
\(d=1\) では source と target が同じである。\(d\ge2\) では \(V\ge6\) なので
\((\beta_2,\beta_3,\beta_4)\le(8,3,0)\) を (N15) が支払う。これで全高次行が成立した。

### 14.5 第一行の無限幅と196個の有限 offset

\(u=2h\) なら \(B_{\rm cap}=\binom{h+4}{2}-9\)、\(u=2h+1\) なら
\(B_{\rm cap}=\binom{h+4}{2}-7\) である。(N9)、(N13) より \(\sigma_C\le h+2\)。従って
\[
\beta_1(G)\le B_{\rm cap}+h+3+1+\lfloor u^2/4\rfloor-u.
\tag{N19}
\]
\(L_1(u)\) からこの右辺を引いた差は、それぞれ
\[
\frac{h(h-7)}2\quad(u=2h),\qquad
\frac{h^2-5h-2}{2}\quad(u=2h+1).
\tag{N20}
\]
偶数は \(h\ge7\)、奇数は \(h\ge6\) で非負である。従って全 \(u\ge13\) と全 \(m,d\) は
\(F_1(m,V)\ge L_1(V)\ge L_1(u)\) により閉じる。

残る範囲は、向きを同一視せず \(3\le u\le12,\ 1\le a<b<u,\ \gcd(a,b,u)=1\) の全196対である。
各対に対して以下の有限アルゴリズムで \(P_C,\sigma_C,H_x,W\) を正確に計算する。
次数 \(n\) の全到達 offset を \(E_0=\{0\}\),
\(E_n=E_{n-1}+\{0,a,b,u\}\) で作る。\(s+t=n,\ B=as+bt\) に対して
\[
(s,t)\in D\ \Longleftrightarrow\ B\notin E_{n-1},\ B-u\notin E_{n-1}\quad(n>0).
\tag{N21}
\]
右辺の二条件はそれぞれ \(x\)、\(v\) を含む表示がないことそのものである。
単位元を加え、(N13) により \(n\le u-2\) だけを調べれば \(D\) を尽くす。
checker は \(n=u-1\) も調べ、その層が空であることを確認する。
\(P_C=|D|\)、\(\sigma_C\) は \((s+1,t),(s,t+1)\notin D\) となる点数、\(H_x\) は (N3) で得る。
巡回群の有向辺 \(r\to r+a,r+b\) に幅優先探索を行えば \(\ell_r\) と \(W\) が得られる。
\(\gcd(a,b,u)=1\) により全頂点に到達する。各行で次の整数を作り、差の非負性を判定する。
\[
U_1=P_C+\sigma_C+1+\min\{W-u,u\max(H_x-2,0)\},\qquad\Delta_1=L_1(u)-U_1.
\tag{N22}
\]

| \(u\) | offset 対数 | 最小 \(L_1(u)-U_1\) |
|---:|---:|---:|
|3|1|−2|
|4|3|−1|
|5|6|1|
|6|9|0|
|7|15|2|
|8|18|4|
|9|27|7|
|10|30|8|
|11|45|14|
|12|42|12|
|計|196||

再現コードは `checks/n4/check_shorter_n4.py`、全196行は
`certificates/n4/SHORTER_N4_CERTIFICATE.json` である。独立実装
`checks/n4/referee_core_audit.py` は次数・offset 法と剰余別 Pareto 極小点法を照合する。
負の差が出るのは \((u,a,b)=(3,1,2),(4,1,3)\) だけであり、順に
\((P_C,\sigma_C,H_x,\widehat R,U_1)=(3,2,0,0,6),(5,2,1,0,8)\) である。
\(d\ge2\) では物理幅はそれぞれ6以上、8以上だから \(L_1(V)\ge16,29\) が支払う。
\(d=1,u=3\) は source と target が同じである。従って残るのは次節の一族だけである。
この有限計算は \(m,d\) を一つも列挙しない。全 \(m,d\) への量化は (N4)、(N5) の証明が担う。

### 14.6 幅4の最後の一族を全 multiplicity で比較する

ここでは \(d=1,u=4,(a,b)=(1,3),m\ge6\) とする。\(S=k[x,y,z,v]\) と置き、
\(C=k[s,st,st^3,st^4]\) の kernel に含まれる四つの二項式をとる。
\[
y^3-x^2z,\qquad yz-xv,\qquad xz^2-y^2v,\qquad z^3-yv^2.
\tag{N23}
\]
内部重み \(\mathrm{wt}(y)=1,\mathrm{wt}(z)=2,\mathrm{wt}(x)=\mathrm{wt}(v)=0\) を先に比較し、
次に通常次数、最後に固定 lex 順で比較する大域的単項式順序を用いる。
左辺の重みは順に \(3,3,4,6\)、右辺は \(2,0,2,1\) なので候補先頭 ideal は
\[
J_0=(y^3,yz,xz^2,z^3).
\tag{N24}
\]
\(A=k[x,v]\) 上の標準列は自由列 \(1,y,y^2,z\) と、\(x\) 指数0に制限された列 \(z^2\) である。
自由列の offset 剰余は \(0,1,2,3\) で相異なる。制限列 \(z^2v^K\) の offset は \(6+4K\)、
次数は \(2+K\)。同じ offset の自由列は \(x^Ly^2v^{K+1}\) だけであり、その次数は
\(L+K+3>2+K\)。同一列の \(L,K\) も次数・offset から一意である。
従って全標準余りの像は線形独立であり、停止する除算により (N23) は完全 Gröbner 基底となる。

列基点 \(b\in\{1,y,y^2,z,z^2\}\) の次数・offset を \((c,n)\) とする。
\(x^Lv^Kb\) の実 weight は \((L+K+c)m+n+4K\) であり、実接錐で消えるのは
この weight に次数 \(L+K+c+j\), \(j\ge1\) の表示があるとき、かつそのときだけである。
\[
r_j=(n-jm)\bmod4,\quad\kappa_j=(jm+r_j-n)/4=\lceil(jm-n)/4\rceil,
\quad\lambda(0)=0,\ \lambda(1)=1,\ \lambda(2)=2,\ \lambda(3)=1.
\tag{N25}
\]
自由 anchor \(1,y,y^2,z\) による競合条件は厳密に
\(K\ge\kappa_j,\ L\ge\Delta_j:=\lambda(r_j)-c-\kappa_j-j\) である。
\(4c-n\ge0\) と \(4\lambda(r)-r\le6\) により
\[
4\Delta_j=(4\lambda(r_j)-r_j)-(4c-n)-j(m+4)\le6-(m+4)<0.
\tag{N26}
\]
従って \(x\) 閾値は常に0である。剰余2には制限 anchor \(z^2\) もあるが、
その必要条件は \(K\ge\kappa_j+1\) であり、自由 anchor が既に覆う。
全標準列を尽くしたので他の競合はない。\(j\ge1\) で \(\kappa_j\) は非減少だから、正確な消滅閾値は
\[
\theta_n=\max\{\lceil(m-n)/4\rceil,0\},\qquad
J:=\operatorname{in}(I_G)=J_0+(b v^{\theta_n}:b=1,y,y^2,z,z^2).
\tag{N27}
\]
この等号も基底から従う。まず (N23) で除算する。(N24) の標準単項式のうち
(N27) で追加禁止されたものは実接錐で0であり、非禁止なものは最大 order がその次数に等しい。
同次数の異なる標準単項式の実 weight は相異なるので、それらは実半群基底の一部として
線形独立である。従って kernel に非禁止余りはなく、先頭 ideal は正確に (N27) となる。
\(J\) の各極小単項式生成元を先頭項に持つ \(I_G\) の同次式を一つずつ選ぶ。
それらによる除算の余りが非零なら、その先頭項は \(J=\operatorname{in}(I_G)\) に属するのに
どの極小生成元でも割れないことになり矛盾する。従って選んだ式は \(I_G\) を生成し、
任意体で \(\beta_1(G)=\mu(I_G)\le\mu(J)\) となる。

\(m=6\) では \(J=(v^2,zv,z^2,yz,y^2v,y^3)\)、従って \(\mu(J)=6<9=F_1(6,4)\)。
\(m>6\) では全 \(\theta_0,\theta_1,\theta_2,\theta_3,\theta_6\) が正であり
\[
J=(xz^2)+J',\quad
J'=(y^3,yz,z^3,v^{\theta_0},yv^{\theta_1},y^2v^{\theta_2},
zv^{\theta_3},z^2v^{\theta_6}).
\tag{N28}
\]
\(J'\) の常在する極小生成元は \(y^3,yz,z^3,v^{\theta_0}\)。残る四候補の極小性条件は順に
\(\theta_1<\theta_0,\theta_2<\theta_1,\theta_3<\theta_0,\theta_6<\theta_3\) である。
\(xz^2\) はこれらのいずれとも可除関係を持たないので \(\mu(J)=\mu(J')+1\)。
\(m=4q+r\) と書けば全剰余の厳密な比較は次のとおりである。

| \(r\) | \((\theta_0,\theta_1,\theta_2,\theta_3,\theta_6)\) | \(\mu(J')\) | \(\mu(J)\) | \(F_1(m,4)\) |
|---:|:---|---:|---:|---:|
|0|\((q,q,q,q,q-1)\)|5|6|7|
|1|\((q+1,q,q,q,q-1)\)|7|8|10|
|2|\((q+1,q+1,q,q,q-1)\)|7|8|9|
|3|\((q+1,q+1,q+1,q,q)\)|5|6|8|

target 列は §1 の公式に \(V=4\) を入れた実際の値である。これで全 \(m\ge6\) の第一行も成立する。
14.4 の全高次行、14.5 の一般第一行と有限196対を合わせ、(N1) の全域で比較が従う。
第0行は双方1、第4行を超える source 行は0である。以上は任意体で成立する計算的証明であり、
公刊入力と196対の有限整数計算を含む。□

## 15 小ordinary領域：83組と5本の無限tail

この節では \(5\le e\le9,\ m\ge e+10\) とし、比較先をactual ordinary
completionとする。第11節のscalarをこの範囲へ拡張せず、独立の上界で処理する。
体 \(k\) は任意とする。

### 15.1 Actual sourceの有限停止とfirst-hit

\(\Gamma=\langle m,m+b_1,\ldots,m+b_{e-1}\rangle\)、\(b_j>0\) と書く。
offset \(A\) を \(b_1,\ldots,b_{e-1}\) で表す最短語長を \(f(A)\) とし、
到達不能または負の \(A\) では \(\infty\)、\(f(0)=0\) とする。
数値指数 \(nm+A\) が長さ \(n\) の表示を持つ条件は \(f(A)\le n\)。
それより長い \(n+j\) の表示を持つ条件は \(f(A-jm)\le n+j\) なので、
offset \(A\) の非零次数基底は正確に
\[
f(A)\le n<g(A),\qquad
g(A)=\min_{j\ge1}\{f(A-jm)-j\}.\tag{O1}
\]
この列で \(x=(t^m)^*\) は \(n\) を1増す。同じ次数の異なるoffsetは異なる
数値指数なので独立であり、\(G\) はこれらの自由列・有限列の直和である。

各剰余 \(r\bmod m\) の最小到達offsetを \(\alpha_r\)、
\(f_r=f(\alpha_r)\) とする。gcd条件から全剰余へ到達し、
\(\alpha_0=f_0=0\)。最小offsetの最短語のprefixも同じ最適性を持つ。
prefix剰余が反復すると正のcycleを除いてoffsetを小さくできるため、
\[
f_r\le m-1.\tag{O2}
\]
\(\alpha_r\) の列は永久に生きる。他の同剰余offsetは
\(A=\alpha_r+jm,\ j\ge1\) なので \(g(A)\le f_r-j\le m-2\)。
従って有限列は次数 \(m-3\) までに終わり、全 \(m\) 本の自由列は次数
\(m-1\) までに始まる。\(h_n=\dim_kG_n\) とすると
\[
1\le h_n\le m,\qquad h_n=m\quad(n\ge m-1).\tag{O3}
\]
上界は同剰余の異なる指数を同次数に二つ置けないことからも分かる。
小さい指数の長さ \(n\) の表示へ \(m\) を加えると、大きい方に長い表示ができる。

\(I=\mathfrak m^n\) は各剰余の最小指数を基底とする
\(k[[t^m]]\)-自由加群rank \(m\) なので \(\ell(I/t^mI)=m\)。
\(t^mI\subset\mathfrak mI\subset I\) より、\(h_n=m\) なら
\(\mathfrak m^{n+1}=t^m\mathfrak m^n\)。これを \(\mathfrak m\) 倍して伝播できる。
従って \(\rho=\min\{n:h_n=m\}\le m-1\) とすると、以後 \(h_n=m\)、
\(x:G_n\to G_{n+1}\) は \(n\ge\rho\) で同型である。
\(G/xG\) は次数 \(\rho\) 以下、\((0:x)\) は次数 \(\rho-1\) 以下にある。
一変数Koszulを先に取る二重複体から
\[
\beta_{i,j}(G)=0\qquad(j>\rho+i).\tag{O4}
\]
ここで \((0:x)(-1)\) の内部次数は \(\rho\) 以下、残る \(e-1\) 変数の
第 \(p\) 鎖群のshiftは \(p\) であることを使った。

有限列 \(A=\alpha_r+jm\) では
\(1\le f(A)<g(A)\le f_r-j\) なので \(j\le f_r-2\)。
\(f_r\) を昇順に並べた \(f_{(j)}\) は \(f_{(j)}\le j\)、
\(0\le j<m\) を満たす。最大長 \(L\) の最適語のprefixが長さ
\(0,\ldots,L\) の異なる剰余を与え、\(j>L\) では全長さが \(L\) 以下だからである。
従って
\[
P_x:=\dim G/xG\le m+\sum_{j=0}^{m-1}\max(j-2,0)
 =\frac{m^2-3m+6}{2}=:P(m),\qquad
\dim(0:x)=P_x-m.\tag{O5}
\]

### 15.2 Truncated lex上界と最後のfirst-hit

\(N_d=\binom{e+d-1}{d}\)、\(2\le\rho\le m-1\) とする。
\(m>N_\rho\) のprofileは存在しない。それ以外について
\[
\widehat h_0=1,\quad\widehat h_1=e,\quad
\widehat h_d=\min(m-1,N_d)\ (2\le d<\rho),\quad
\widehat h_d=m\ (d\ge\rho)\tag{O6}
\]
と置く。actual列は \(\rho\) より前で \(h_d\le\widehat h_d\)。

\(X_1>\cdots>X_e\) のlex順で、次数 \(d\) の小さい方から \(h\) 個の
単項式のうち \(X_1,\ldots,X_j\) のみを使う個数を \(S_j(d,h)\) とする。
lex商の最大変数 \(j\)、次数 \(d\) の極小生成元数はstable shadowの対応から
\[
g_j(d)=S_j(d-1,h_{d-1})-S_j(d,h_d)+S_{j-1}(d,h_d).\tag{O7}
\]
\(w_j=\binom{j-1}{i-1}\) を掛け、\(d=2,\ldots,\rho+1\) について
telescopingすると、次数cutoff (O4) とBHP/EKにより
\[
\begin{aligned}
\beta_i(G)&\le L_i(h,\rho),\\
L_i(h,\rho)&=i\binom{e+1}{i+1}
 -\sum_{j=1}^eS_j(\rho+1,m)w_j
 +\sum_{d=2}^{\rho+1}\sum_{j=1}^eS_{j-1}(d,h_d)w_j.
\end{aligned}\tag{O8}
\]
負のterminal項と \(d=\rho,\rho+1\) の項は固定され、他の \(S_j\) は
\(h\) に関して非減少なので、全行で同時に
\[
\beta_i(G)\le L_i(h,\rho)\le L_i(\widehat h,\rho).\tag{O9}
\]
右辺をformalな整数式として評価すれば十分であり、\(\widehat h\) を数値半群の
Hilbert関数として実現する必要はない。

ここで \(L_i(\widehat h,\rho)\) の全 \(\rho\) に対する共通最大点が
\(\rho=m-1\) であることを示す。以下 \(e\ge5,m\ge15\)。
最大変数 \(j\) のtruncated生成元総数を \(T_j(\rho)\) と書く。
次数 \(m\) の小さい方から \(m\) 個は全て \(X_e\) を含み、次数 \(m-1\) では
\(X_e\) を含まないものは \(X_{e-1}^{m-1}\) だけなので、
\[
\begin{aligned}
T_j(m-1)&=j+\sum_{d=2}^{m-2}S_{j-1}(d,b_d) &&(j<e),\\
T_e(m-1)&=e-m+1+\sum_{d=2}^{m-2}S_{e-1}(d,b_d),
\quad b_d=\min(m-1,N_d).
\end{aligned}\tag{O10}
\]
\(\rho\le m-2\) の次数 \(\rho\) の \(m\) 番目のlex最小単項式を \(v\)、
\(a=\maxvar(v)\)、\(k=e-a\) と置く。\(\rho\) 以後のcapは \(m-1\) なので、
共通項を消すと \(j<e\) で
\[
T_j(m-1)-T_j(\rho)
 =S_j(\rho+1,m)-S_{j-1}(\rho+1,m)-[j>a]
  +\sum_{d=\rho+1}^{m-2}S_{j-1}(d,m-1)
 \ge-[j>a].\tag{O11}
\]
負slotは高々 \(k-1\) 個、損失は各1以下である。
\(\rho\le m-3\) で \(A=[k\ge1]\)、
\(B=[\maxvar(v_{\rho+1,m})\le e-1]\) と置くと
\[
T_e(m-1)-T_e(\rho)
 =1-A-B+\sum_{d=\rho+2}^{m-2}S_{e-1}(d,m-1).\tag{O12}
\]
各和項は1以上。純冪 \(X_{e-1}^d\) のlex rankが \(d+1\le m-1\) だからである。

\(k=0\) では \(A=0,B\le1\) より差は非負。
\(k=1,\rho\le m-4\) では一項が不足を払う。
\(k=1,\rho=m-3\) では次数 \(m-2\) の \(m\) 番目は
\(X_{e-2}X_e^{m-3}\) なので \(B=0\)、和が空でも差は0。
\(k\ge2\) では \(X_a^\rho\) が末尾 \(k+1\) 変数の最後にあるため
\(\binom{\rho+k}{\rho}\le m\)。
\(\rho,k\ge2,\rho+k\ge5\) なら
\(\binom{\rho+k}{\rho}\ge\binom{\rho+k}{2}\ge\rho+k+3\)。
\((\rho,k)=(2,2)\) も \(m\ge15\) により \(m-\rho\ge k+3\)。
よって(O12)は \(-1+(m-\rho-3)\ge k-1\)。
\(\rho=m-2\) では同じ \(m\) 番目の単項式から \(k=0\)、
(O10),(O8)を直接引くとslot \(e\) の差は0、他は非負。
\(\rho=m-1\) は等号である。

従って最後のslotの増分は全負slotを払う。
EK重み \(w_j\) は非負で \(j\) に関して非減少なので、
\[
L_i(\widehat h,\rho)\le L_i(\widehat h,m-1)\quad\text{全 }i.\tag{O13}
\]
これは隣接する \(\rho\) 間の単調性を仮定せず、共通最大点を直接示す論証である。

### 15.3 五本の無限tail

同Hilbert関数のlex標準単項式について、次数 \(d+1\) の子 \(v\) から親
\(v/X_j\) へ重み \(v_j/(d+1)\) を付ける。子への総重みは1、各親からの総重みは
\((d+e)/(d+1)\) 以下。新生成元数はそのshadowから次の標準単項式数を引いたものなので、
(O4)、\(h_1=e,h_m=m,h_d\le m\) でtelescopingすると
\[
\beta_1(G)\le
(e-1)m\mathcal H_m-\frac{(3e-1)m}{2}
 +\frac{e(e+1)}2=:A_e(m).\tag{O14}
\]
\(D_e(m)=\binom m2-A_e(m)\) に対し
\[
\Delta D_e=m+\frac{e+1}{2}-(e-1)\mathcal H_m,\qquad
\Delta^2D_e=1-\frac{e-1}{m+1}.\tag{O15}
\]
以下は有限有理和から得る厳密なanchorである。

| \(e\) | \(T_e\) | \(D_e(T_e)\) | \(\Delta D_e(T_e)\) |
|---:|---:|---|---|
|5|16|\(28529/45045\)|\(986861/180180\)|
|6|24|\(87527047/14872858\)|\(3076971505/356948592\)|
|7|32|\(13190245423022/1504203675975\)|\(280360191738961/24067258815600\)|
|8|42|\(17040044863244869/474156254847600\)|\(46124404177135267/2844937529085600\)|
|9|54|\(42360392440805889237573/380206848900550521850\)|\(153275837511203454076291/6843723280209909393300\)|

全anchorが正で、以後の第二差分も正なので、全 \(m\ge T_e\) の第一行が閉じる。

他の \(e-1\) 変数と一変数 \(x\) のKoszul二重複体、(O5)から
\[
\beta_i(G)\le P(m)\binom ei-m\binom{e-1}{i-1}=:U_e(m,i).\tag{O16}
\]
\(G_e(m)=2\binom m3-U_e(m,2)\) とすると
\[
\begin{aligned}
12G_e(m)&=4m^3-[12+3e(e-1)]m^2
 +[8+3(e-1)(3e+4)]m-18e(e-1),\\
\Delta G_e(m)&=m^2-[1+e(e-1)/2]m+(e-1)(e+2)/2,\\
\Delta^2G_e(m)&=2m-e(e-1)/2,\qquad \Delta^3G_e(m)=2.
\end{aligned}\tag{O17}
\]

| \(e\) | \(T_e\) | \(G_e(T_e)\) | \(\Delta G_e(T_e)\) | \(\Delta^2G_e(T_e)\) |
|---:|---:|---:|---:|---:|
|5|16|114|94|22|
|6|24|343|212|33|
|7|32|305|347|43|
|8|42|238|581|56|
|9|54|360|962|72|

第三差分とanchorが正なので、全 \(m\ge T_e\) の第二行も閉じる。
\(F_i=i\binom m{i+1}\) とすると \(m\ge e+1,\ 2\le i<e\) で
\[
\frac{F_{i+1}/\binom e{i+1}}{F_i/\binom ei}
 =\frac{(i+1)^2(m-i-1)}{i(i+2)(e-i)}>1,\qquad
\frac{U_e(m,i)}{\binom ei}=P(m)-\frac{mi}{e}.\tag{O18}
\]
前者は \(m-i-1\ge e-i\)、\((i+1)^2>i(i+2)\) による。
後者は \(i\) とともに減少するので、第二行の比較が全高次行を払う。

### 15.4 必要な有限整数補題

残る \(e+10\le m<T_e\) は次の83組である。
\[
\begin{array}{c|c|c}
e&m&\text{組数}\\ \hline
5&15&1\\
6&16,\ldots,23&8\\
7&17,\ldots,31&15\\
8&18,\ldots,41&24\\
9&19,\ldots,53&35
\end{array}
\]
各組で \(\rho=m-1\) の列 (O6) だけを作り、(O8)を全 \(1\le i\le e\) で評価する。
\(S_j(d,h)\) は指数をlex順に分ける再帰的な二項係数計数で求め、
各 \(i\) の重みは整数 \(\binom{j-1}{i-1}\) とする。
この明示有限補題の実行結果は83組・665行比較、全不足0、
最小余裕は \(105-38=67\) である。
再現コードは <code>checks/verify_small_ordinary.py</code>、
全証書は <code>certificates/small_ordinary.json</code>。
同じコードが(O14)–(O17)の全有理anchorと差分も再計算する。

(O9),(O13)が全first-hitと全actual Hilbert列をこの有限補題へ還元し、
第15.3節が無限tailを扱う。従って
\[
5\le e\le9,\quad m\ge e+10
\quad\Longrightarrow\quad
\beta_i(G)\le i\binom m{i+1}\quad(i\ge1).\tag{OSM}
\]
第0行は双方1、\(i>e\) のsource行は0である。
有限計算の出力だけから全半群へ外挿したのではなく、(O1)–(O18)がその全称性を保証する。

## 16 全領域の合成

まず \(e\le2\) を扱う。\(e=1\) の数値半群は \(\mathbb N\) でsourceとtargetが等しい。
\(e=2\) では \(\Gamma=\langle m,n\rangle\)、\(m<n,\gcd(m,n)=1\)。
定義式 \(y^m-x^n\) の最低次数項から \(G_\Gamma=k[x,y]/(y^m)\)、
Betti列は \((1,1)\) である。completionは埋込次元2以上の1次元環なので、
その定義理想は非零、第一Betti数は1以上。それ以後のsource行は0である。

以下 \(e\ge3\)、物理幅 \(w=g_e-m\) とする。

1. **\(w\le m-2\)。** \(e=3\) は第1.2節のLan–Tu–Vu。
   \(e=4\) は第14節。\(e\ge5\) は \(d=\gcd(g_2-m,\ldots,g_e-m)\) と
   \(u=w/d\le w<m\) により第13節の仮定を満たす。
   \(\gcd(m,d)=1\) と正規化offsetのgcd条件は数値半群のgcdから従う。
2. **\(w\ge m-1\)。** completionのactual atomは正確に
   \(m,m+1,\ldots,2m-1\)。第4節で一つのcutを選ぶ。
   \(r=2,3\) は第9節で全 \(\delta\) を処理する。
   \(r\ge4\) では \(r\le e-1\) より \(e\ge5\)、さらに
   \(\delta\ge a\ge\binom{r+1}{2}\ge10\)。
   \(e\ge10\) は第11節の固定cutoff scalarを第10節へ適用し、
   \(5\le e\le9\) は \(m=e+\delta\ge e+10\) により第15節を適用する。

幅は整数なので二つの領域は全域を排他的に覆う。\(w=m-1\) もordinary側に含む。
各補題は全Betti行を処理し、sourceの表示変数数を超える行は0、第0行は1である。
一般形式を使う第4節だけは無限な純超越拡大へ移り、Betti数の同標数の
体拡大不変性で元の体へ戻す。他の新しい評価は整数基底・数値的有理不等式・
各体上のKoszul複体による。従って(P14)が任意体上で成立する。□

## 17 計算支援部分と形式化の境界

本稿は、第1.2節の公刊定理と、本文で有限化を証明した厳密整数補題を用いる
人間向けの計算支援証明である。必須の有限データは次の二つである。

| 箇所 | 有限範囲 | 計算するもの |
|---|---|---|
|第14節|正規化幅 \(3\le u\le12\) の196 oriented offset組|全 \(m,d\) に一様な第一行上界。二つの不足例は本文で処理|
|第15節|小ordinaryの83組、665行比較|全actual Hilbert列に対する共通上界。無限tailは5本の有理anchorと差分|

第11節の有限有理比較・barrier恒等式、第13–14節の多項式係数も付属コードが
定義式から検算する。有限のsourceサンプルから無限領域へ推測する手順は用いない。
証書のハッシュはファイル同一性の記録であり、数学的な導出の代わりではない。

Leanへ移す際には、数値座標とjump filtration、TorとKoszulの補題、
公刊定理の正確なstatement、そして上記有限補題のkernel内検証を接続する必要がある。
本稿ではLeanファイル・toolchain・未証明axiomによる仮の形式証明は追加していない。
再実行手順、依存表、全域coverage、置換台帳、統合監査を本稿とともに保存する。
