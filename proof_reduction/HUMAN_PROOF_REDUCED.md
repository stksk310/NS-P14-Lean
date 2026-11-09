# NS P14 人間向け縮約証明

2026年11月9日。これは論文化前の数学的作業稿である。新しく示した簡約と継承する境界を区別する。

**ordinary側は10生成元以上を単一scalarで、3・4生成元を小cutで処理する。幅側は5生成元以上を有限coreなしで処理する。最後の独立認証未完は、物理幅が狭い4生成元の境界N4である。従って現段階でP14の無条件完全証明済みとは宣言しない。**

## 1 問題と最後に残す境界

真正な数値半群 \(\Gamma=\langle m=g_1<\cdots<g_e\rangle\)、任意体 \(k\) に対し、\(\delta=m-e\)、\(G=\operatorname{gr}_{\mathfrak m}k[[t^\Gamma]]\)、\(\widetilde\Gamma=\langle m,m+1,\ldots,g_e\rangle\) とする。各環自身の最小多項式表示に関するtotal Betti数について
\[
 \beta_i(G;k)\le\beta_i(G_{\widetilde\Gamma};k)\quad(i\ge0) \tag{P14}
\]
を考える。範囲外の二項係数は0とする。

本稿で独立認証を完了していない境界は、次の一つに絞る。

**N4：4個のactual atomを持ち、物理幅 \(g_4-m\le m-2\) のsourceは、任意体・全行のP14を満たす。**

元資料にはこの定理の証明と再現可能なコードがある。しかし本稿はその全祖先までの独立査読を終えたとはしない。N4を数学的入力として採用したときに全域へ至る証明を示す。正確な根拠・監査状態は [依存台帳](DEPENDENCY_AND_GAP_LEDGER.md) に記す。

その他の境界は次の通りである。3生成元は[Lan–Tu–Vuの公刊定理](https://arxiv.org/html/2307.05589v1#S1)を使う。幅側 \(u<m\) は5生成元以上を有限coreなしで閉じる [幅側補題](WIDTH_REDUCTION_PROOF.md) を使う。ordinaryの5〜9生成元に残る小部分は [小ordinary補題](SMALL_ORDINARY_PROOF.md) の83組の整数評価と5本の無限tailで処理する。以下の中心鎖は、Elias・Peeva・EKを使用しない。BHP/EKは幅側・小ordinary側のlex評価には残る。

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

すべてのjumpは \(d\le\nu\) を満たす。これを確認するため \(Q=S_0/I_Q\)、\(A=S_0/I_A\) と書く。\(Q_{\nu+1}=0\) なので \(I_Q\) は次数 \(\nu+1\) 以下で生成され、\(N=I_Q/I_A\) も同じ次数上界を持つ。座標極小生成元headの次数からjumpは \(\nu\) 以下であり、以後の生きた \(N\)-作用ではjumpが増えない。これですべてのhead、したがってすべてのterminalに上界が伝播する。

## 3 最短offset経路だけで総量を評価する

Eliasのmicroinvariant定理を使わず、必要な上界を初等的に証明する。
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
以下 \(V=e+\delta/2-3/2\)、\(M=m-1\) と書く。この \(V\) は幅とは別の数値資源である。すべての議論は数値半群の中で行われ、体や標数に依存しない。

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
 S=\sum_{\rho\ne0}(L_\rho-1)\le\delta V. \tag{5.2}
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

この追加上界を捨てないことが、本稿の依存削減の要点である。

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

この証明ではPeeva、EK、lex、couplingを使わない。有限長と単一次数生成という仮定は、それぞれ総和の有限性と同shiftの表示に使用した。

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
 P_G(z)\preceq T_{e-r+1}(z)
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
 &=V\left[\binom{\delta+r-1}{j}-\binom{r-1}{j}\right]+\Gamma_j,\\
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

従って、ここでの \(V\ge0\) に対し

\[
 R_j-L_j\ge\delta(V+1)\binom{r-1}{j-1}. \tag{8.4}
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
\(S\le\delta V\) とし、前者は \(V\le3\)、後者は \(V\ge3\) で \(\delta(V+1)\) 以下となる。従ってすべての \(V\) で第一rankが払える。top rankも
\[
 c_2(G)\le\sum_{t\ge1}H_t/t\le S-\delta\le\delta(V-1)
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
 \delta(V+1)-[\tfrac43\delta+\tfrac43(M-6)+\tfrac23\delta V]
 =\frac{\delta(V-1)-4(M-6)}3\ge0.
\]
実際、\(z=\delta-6\ge0\) と書けば分子は
\((z+2)e+\binom z2+7>0\)。第二rankは \(V\ge2\) から \(2\delta(V+1)\) 以下、top rankも払える。実際の3本cutには \(e\ge4\)、\(\delta\ge6\) が必要なので \(V\ge11/2>2\) である。

従ってordinary targetを持つ3・4生成元sourceはすべてこの節で閉じ、旧小生成元数定理を呼ばない。

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
 F_r\le\delta(V+1) \tag{10.2}
\]

を証明すればよい。

## 11 単一scalarの全域証明

### 結論

cutoff を \(D=\lfloor\delta/2\rfloor+1\) とし、既存の一列の上界に
\(H_1\le M-a_r\) を保持する。このとき **全ての整数**

\[
 e\ge10,\qquad r\ge4,\qquad\delta\ge a_r=\frac{r(r+1)}2
\]

について、改善gapは狭義に正である。
したがって actual cut の \(r\) へ直接適用でき、\(p(\delta)\) や最大rankへの数値包絡は不要である。
\(\delta\ge210\) を別扱いする調和数帰納も不要である。
必要な有限算術は \(\mathcal H_{23}<747/200\) の1個、
小さな有理式7個、非負係数の多項式恒等式1個である。

以下は scalar の独立証明である。既存のPASS値を根拠にしない。
半群構造、資源列の不等式、targetへの移行は別途必要である。

### 1. cutoff を残した同じ資源列の上界

\[
 M=e+\delta-1,\quad V=e+\frac\delta2-\frac32,\quad
 \mathcal H_D=\sum_{u=1}^D\frac1u,
\]
\[
 \alpha=\frac{r-1}{D+1},\quad c=\frac{r+1}2-\alpha,
 \qquad D=\lfloor\delta/2\rfloor+1.
\]

ここで \(D\ge6\)、\(D\ge r\)、\(\alpha<1\)、\(c>0\) である。
\(D\ge r\) は \(D\ge\lfloor a_r/2\rfloor+1\ge r\) から従う。

既存の scalar

\[
 F_r=(r-1)\delta+\frac{r+1}2H_1+
                 \sum_{t\ge2}\frac{r-1}{t+1}H_t
\]

に対して、\(t\ge D\) の重みを \(\alpha\) で評価する。
\(H_0=\delta\)、\(\sum_tH_t\le\delta V\)、\(H_t\le M\)、
\(H_1\le M-a_r\) により

\[
\begin{aligned}
F_r\le\widehat U_r={}&\alpha\delta V+(r-1-\alpha)\delta
 +c(M-a_r)\\
 &+M\sum_{t=2}^{D-1}\left(\frac{r-1}{t+1}-\alpha\right).
\end{aligned}
 \tag{1}
\]

この有限和を足すと

\[
 \widehat U_r=M+(r-1)K_D-ca_r,
\]
\[
 K_D=\delta+\frac{\delta(V-1)}{D+1}
       +M\left(\mathcal H_D-2+\frac2{D+1}\right).
 \tag{2}
\]

同じ資源列の \(H_1\) の正の係数の上界を置き換えたものであり、
\(H_1\) を二重に消費していない。

以下、\(D\) を一時的に独立変数とし、

\[
 G_r(e,d;D)=d(V+1)-\widehat U_r,
 \qquad D(d)=\lfloor d/2\rfloor+1
\]

と書く。\(G_r(e,d;D)\) の \(e\) の係数は

\[
 A_r(d;D)=d-1-(r-1)\left(\mathcal H_D-2+\frac{d+2}{D+1}\right).
 \tag{3}
\]

\(G_r(10,d;D(d))>0\) と \(A_r(d;D(d))>0\) を示せばよい。

### 2. 三角数基点を調和数閾値へ

固定した \(r\ge4\) について \(a=a_r\)、\(D_0=D(a)\) と置く。
\(e=10,d=a\) では \(M=a+9,V=(a+17)/2\) だから、直接整理により

\[
 G_r(10,a;D_0)=(r-1)(a+9)(T_r-\mathcal H_{D_0}),
\]
\[
 T_r=\frac{a(a+22-r)}{2(r-1)(a+9)}+\frac{2r-3}{r-1}
       -\frac{a(a+21)+36}{2(D_0+1)(a+9)}.
 \tag{4}
\]

全ての \(r\ge4\) で \(\mathcal H_{D_0}<T_r\) を示す。

### 3. 唯一の調和数アンカーと6基点

\[
 \mathcal H_{23}=\frac{444316699}{118982864}<\frac{747}{200},\qquad
 \frac{747}{200}-\mathcal H_{23}=\frac{2107451}{2974571600}>0.
 \tag{5}
\]

\(D\le23\) なら、Cauchy の不等式、または算術平均・調和平均から

\[
 \sum_{u=D+1}^{23}\frac1u\ge\frac{2(23-D)}{D+24}.
\]

実際、項数 \(k=23-D>0\) のとき分母の総和は \(k(D+24)/2\) であり、
\((\sum1/u)(\sum u)\ge k^2\) を使う。\(k=0\) のときも両辺0である。
従って

\[
 \mathcal H_D<\frac{747}{200}-\frac{2(23-D)}{D+24}.
\]

以下の6個の正の有理数だけで \(4\le r\le9\) が閉じる。

| \(r\) | \(D_0\) | \(T_r\) | \(T_r-747/200+2(23-D_0)/(D_0+24)\) |
|---:|---:|---:|---:|
| 4 | 6 | \(1126/399\) | \(17587/79800\) |
| 5 | 8 | \(35/12\) | \(143/1200\) |
| 6 | 11 | \(623/200\) | \(23/350\) |
| 7 | 15 | \(745/222\) | \(2993/96200\) |
| 8 | 19 | \(622/175\) | \(321/60200\) |
| 9 | 23 | \(269/72\) | \(1/900\) |

### 4. rank 方向の帰納

\(\varepsilon_r=a_r-2\lfloor a_r/2\rfloor\in\{0,1\}\) とし、

\[
 T_\varepsilon(r)=\frac{a(a+22-r)}{2(r-1)(a+9)}+\frac{2r-3}{r-1}
       -\frac{a(a+21)+36}{(a+4-\varepsilon)(a+9)}.
\]

すると \(T_r=T_{\varepsilon_r}(r)\)、かつ
\(T_1(r)\le T_r\le T_0(r)\) である。
付録の正係数恒等式から

\[
 T_1(r+1)-T_0(r)>\frac2r\qquad(r\ge10).
 \tag{6}
\]

一方、\(b=D(a_{r+1})-D(a_r)\le(r+2)/2\)、
\(D(a_r)+1\ge(a_r+3)/2\)、\(D(a_{r+1})\ge(a_{r+1}+1)/2\) である。
\(u\mapsto1/u\) の凸性から、端点を結ぶ直線以下の値を足すと

\[
\begin{aligned}
 \mathcal H_{D(a_{r+1})}-\mathcal H_{D(a_r)}
 &\le\frac b2\left(\frac1{D(a_r)+1}+\frac1{D(a_{r+1})}\right)\\
 &\le\frac{r+2}2\left(\frac1{a_r+3}+\frac1{a_{r+1}+1}\right)
 <\frac2r.
\end{aligned}
 \tag{7}
\]

最後の差は

\[
 \frac{8(r^2+3r+6)}{r(r^2+r+6)(r^2+3r+4)}>0.
\]

残る \(r=9\to10\) は \(D(a_9)=23,D(a_{10})=28\) に対して

\[
 \mathcal H_{28}-\mathcal H_{23}
 \le\frac52\left(\frac1{24}+\frac1{28}\right)
 =\frac{65}{336}<\frac15,
\]
\[
 T_{10}-T_9-\frac15=\frac{293}{18560}>0.
 \tag{8}
\]

従って第3節と帰納により、全ての整数 \(r\ge4\) で

\[
 G_r(10,a_r;D(a_r))>0.
 \tag{9}
\]

### 5. slope は d とともに増える

固定した \(r\ge4\) に対し \(d\ge a_r\) とする。
\(n=D(d)\)、\(\alpha_n=(r-1)/(n+1)\) と書く。
(3) を直接差し引くと、偶数 \(d\) から奇数へは

\[
 A_r(d+1;D(d+1))-A_r(d;D(d))=1-\frac{r-1}{n+1}>0,
\]

奇数 \(d\) から偶数へは

\[
 A_r(d+1;D(d+1))-A_r(d;D(d))
 =1-\frac{2(r-1)}{(n+1)(n+2)}>0.
 \tag{10}
\]

いずれも \(n\ge r\) を使った。従って chosen cutoff の slope は増加する。
また \(\alpha_{D(d)}\) は非増加である。

### 6. 基点正性から gap の全 d 単調性と正 slope へ

\(a=a_r\)、\(D_0=D(a)\)、\(A_0=A_r(a;D_0)\) とする。
直接整理すると

\[
 G_r(10,a;D_0)=(a+9)A_0+C,
\]
\[
 C=\frac{a[-a(D_0-r+2)-D_0(r-4)+3]}{2(D_0+1)}<0.
 \tag{11}
\]

\(D_0\ge r\)、\(a\ge10\)、\(r\ge4\) により括弧は高々 \(-2a+3<0\) である。
(9), (11) から

\[
 A_0>\frac{-C}{a+9}>0.
 \tag{12}
\]

cutoff \(D=n\) を固定して \(d\) を一つ増やす差は

\[
 G_r(10,d+1;n)-G_r(10,d;n)
 =A_r(d;n)+11-r-\frac{8(r-1)}{n+1}.
 \tag{13}
\]

(10), (12) と \(n\ge D_0\) により、(13) は

\[
 F_\varepsilon:=\frac{-C}{a+9}+11-r-\frac{8(r-1)}{D_0+1}
 \tag{14}
\]

より大きい。ただし \(\varepsilon=a-2\lfloor a/2\rfloor\in\{0,1\}\)、
\(D_0=(a-\varepsilon)/2+1\) である。
\(F_\varepsilon\) を \(a,r\) の有理式とみなすと、直接通分により

\[
 F_0-F_1=\frac{(r-1)(a^2+17a+144)}{(a+3)(a+4)(a+9)}>0,
\]
\[
 F_1=\frac a2-\frac{3r}2+\frac{11}2
       +\frac{3(5r+31)}{2(a+9)}-\frac{17(r-1)}{a+3}.
 \tag{15}
\]

\(r\ge4\) に対して

\[
 \frac a2-\frac{3r}2+\frac{11}2
 =\frac{r^2-5r+22}4\ge\frac92,
\]
\[
 a+3-4(r-1)=\frac{(r-3)(r-4)}2+1>0.
\]

従って

\[
 F_\varepsilon\ge F_1>\frac92-\frac{17}4=\frac14.
 \tag{16}
\]

偶数 \(d\) からのstepでは cutoff は変わらないので、(13), (16) で gap が増える。
奇数 \(d=2n-1\) からは、まず cutoff \(n\) のまま \(d+1=2n\) に増やし、
次に cutoff を \(n+1\) に増やす。後者による追加差は

\[
 G_r(e,2n;n+1)-G_r(e,2n;n)
 =\frac{r-1}{(n+1)(n+2)}\,[n(e-4)+a_r]>0
 \quad(e\ge10).
 \tag{17}
\]

よって \(G_r(10,d;D(d))\) は \(d\ge a_r\) で毎step \(1/4\) より大きく増加する。
(9) と合わせ全域で正であり、(10), (12) から slope も全域で正である。
最後に

\[
 G_r(e,d;D(d))=G_r(10,d;D(d))+(e-10)A_r(d;D(d))>0
 \qquad(e\ge10).
 \tag{18}
\]

これが結論である。actual \(r\) に直接使えるので、最大rankへの包絡は不要。

### 付録：rank差分補題 (6) の正係数恒等式

直接通分すると

\[
 T_1(r+1)-T_0(r)-\frac2r=\frac{P(r)}{Q(r)},
\]
\[
\begin{aligned}
 P(r)={}&r^{10}-r^9-18r^8-426r^7-1543r^6-10513r^5\\
        &-22712r^4-78276r^3-27568r^2-57088r+175104,
\end{aligned}
\]
\[
 Q(r)=4r(r-1)(r^2+r+8)(r^2+r+18)(r^2+3r+8)(r^2+3r+20)>0.
\]

\(t=r-10\ge0\) と置けば

\[
\begin{aligned}
 P(t+10)={}&t^{10}+99t^9+4392t^8+114534t^7+1934237t^6\\
 &+21934307t^5+167027138t^4+823740244t^3\\
 &+2388816952t^2+3111610752t+37151424>0.
\end{aligned}
\]

これは整数係数の恒等式であり、調和数や無限の数値検算を含まない。
付属 `checks/verify_scalar.py` は定義式から有理多項式を構成し、
(E3相当の) 通分後の全係数一致と、この平行移動後の全係数一致を厳密に検査する。

### 独立検証コード

`checks/verify_scalar.py` は (5)、第3節の6個の正有理式、(8) の1個、付録の係数恒等式を再計算する。
`--diagnostic N` は更に \(10\le\delta\le N\)、\(r=p(\delta)\) において、
元の重み付き上界 (1) とgapの恒等式、slopeの差分、固定cutoffのgap差分、
cutoff増加差分、基点の \(C,F_\varepsilon\) の恒等式を全て厳密有理数で独立診断する。
診断は紙上の普遍帰納の代わりではない。

独立数学レビューでも、上界・threshold・rank帰納の多項式全係数・delta差分を再導出し、式誤りや量化の穴は見つからなかった。診断コードは各deltaの最大許容rankだけを検査し、全許容組を列挙するものではない。全actual rankの主張は本稿の帰納証明による。

## 12 残る境界と最終組立て

物理幅 \(w=g_e-m\) で二つに分ける。

1. **proper narrow：\(w\le m-2\)。** \(e\ge5\) なら \(u=w/d\le w<m\) なので幅側補題で閉じる。\(e=4\) はN4、\(e=3\) はLan–Tu–Vuの定理を使う。\(e\le2\) は下記の直接計算でよい。
2. **ordinary：\(w\ge m-1\)。** completionの最小生成系は \(m,m+1,\ldots,2m-1\)。\(e\ge3\) で第4節のcutを一つ選ぶ。\(r=2,3\) は第9節。\(r\ge4\) なら \(\delta\ge a\ge\binom{r+1}{2}\ge10\) であり、\(e\ge10\) は第10–11節で同じcutの全rankが払える。残る \(5\le e\le9\)、\(\delta\ge10\) は小ordinary補題を使う。

\(e=1\) は \(\Gamma=\mathbb N\)。\(e=2\) は \(\Gamma=\langle m,n\rangle\)、\(G=k[x,y]/(y^m)\) なのでBetti列は \((1,1)\)。実際のcompletionは埋込次元2以上の1次元環なので第一Betti数が1以上、以後のsource行は0となる。すべてのtargetで比較が成立する。

境界 \(w=m-1\) はordinaryとして第2の場合に含まれる。正規化幅を物理幅と取り違えず、全段階で実際のcompletionを比較先に保った。有限体は第4節の純超越拡大とintrinsic Betti数の不変性で戻す。

従って、N4および明記した公刊入力を採用すれば、P14は全真正数値半群・任意体・全total Betti行で成立する。□

## 13 Leanへ渡す依存

中心鎖は数値座標、jump strata、実際の塔、一つの \(H_t\) 列、直接Koszul評価、単一scalar、ordinary target比較である。N4以外の旧閉鎖集合を公理としてまとめて受け取る必要はない。

まずH23の有理数評価、7個の小有理数不等式と整数多項式恒等式を形式化できる。その次に直接Koszulの単位小行列補題、塔のTor完全列、数値座標をつなぐ。幅側はKneser/BHP/EK/算術列公式と端点移行、小ordinary側はBHP/EKと83組の整数比較へ分離する。

N4、古典、整数計算のJSONを未証明の `axiom` として置いた段階をP14全域のLean完全証明と呼ばない。本成果にはLeanファイルやtoolchainを追加していない。

