# NS-P14：一本に統合した証明稿

2026年11月9日。論文化前・Lean形式化前の数学的作業稿。

本稿はP14の全域を、一つの依存関係を持つ証明にまとめる。前版で独立認証を保留していたN4は、第12節で証明する。公刊定理を明示して使い、有限残余は証明付きの有限化と厳密整数プログラムにより評価する。従って本稿の資格は**計算支援を含む人間向けの証明稿**であり、Leanによる形式検証済みという意味ではない。

本文第2–11節はordinary側の共通鎖、第12節は四生成元の狭幅、第13節で全場合を合成する。幅側の補助証明、小ordinaryの有限化、一般端点移行、一欠落幅の証明を付録に収める。式番号と節番号は、各補助証明内で局所的に読む。

必要な有限計算は、小ordinaryの83組・665比較と、N4の13,921 offset組・4,824有限点・108 tailである。後二者の4,824点には要求範囲より広い \(m=w+1\) の108点も含み、真の狭幅部分は4,716点。有限点からの外挿をせず、無限範囲は本文中の上界・停止・安定tailで処理する。Taylor rankの有限証明書は最終証明には不要である。

## 1 主定理と証明の構成

真正な数値半群 \(\Gamma=\langle m=g_1<\cdots<g_e\rangle\)、任意体 \(k\) に対し、\(\delta=m-e\)、\(G=\operatorname{gr}_{\mathfrak m}k[[t^\Gamma]]\)、\(\widetilde\Gamma=\langle m,m+1,\ldots,g_e\rangle\) とする。各環自身の最小多項式表示に関するtotal Betti数について
\[
 \beta_i(G;k)\le\beta_i(G_{\widetilde\Gamma};k)\quad(i\ge0) \tag{P14}
\]
を考える。範囲外の二項係数は0とする。

第12節で次の四生成元補題を証明し、主定理に組み込む。

**N4：4個のactual atomを持ち、物理幅 \(g_4-m\le m-2\) のsourceは、任意体・全行のP14を満たす。**

N4は以下で証明する内部補題である。原資料の閉鎖宣言や過去のPASS表示は仮定せず、必要な定義・支持分類・無限tailを証明し、残る有限整数計算を別実装で完全評価する。

その他の境界は次の通りである。3生成元は[Lan–Tu–Vuの公刊定理](https://arxiv.org/html/2307.05589v1#S1)を使う。幅側 \(u<m\) は5生成元以上を有限coreなしで閉じる 付録Aの幅側補題 を使う。ordinaryの5〜9生成元に残る小部分は 付録Bの小ordinary補題 の83組の整数評価と5本の無限tailで処理する。以下の中心鎖は、Elias・Peeva・EKを使用しない。BHP/EKは幅側・小ordinary側のlex評価には残る。

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


## 12 四生成元の真の狭幅補題N4

### 12.1 正確な定理・外部入力・場合分け

任意の体 \(k\)、真正数値半群 \(\Gamma=\langle m,g_2,g_3,g_4\rangle\) で、物理幅 \(w=g_4-m\le m-2\) とする。\(d=\gcd(g_2-m,g_3-m,g_4-m)\) と置くと、一意に
\[
\Gamma=\langle m,m+da,m+db,m+du\rangle,
\quad0<a<b<u,\quad \gcd(a,b,u)=\gcd(m,d)=1,
\quad du=w\le m-2
\]
となる。以下で全 \(i\) に対するactual interval completionとの比較を証明する。\(d\ge2\) は12.3、\(d=1\) の高次行は12.4、第一行は12.5–12.6で尽くす。第0行は双方1、第4行を超えるsource行は0である。

比較先の一般公式を先に固定する。物理幅 \(V<m\) の区間完備化について、\(D=V-((m-1)\bmod V)\in\{1,\ldots,V\}\) とすれば
\[
F_i(m,V)=i\binom V{i+1}+
\begin{cases}(D+1-i)\binom V{i-1},&i\le D,\\
(i-D)\binom Vi,&i>D.
\end{cases}\tag{N4-T}
\]
これはGimenez–Sengupta–Srinivasan [Theorem 4.1](https://arxiv.org/pdf/1108.3203) の算術列半群環の公式と、Herzog–Stamate [Proposition 2.5](https://arxiv.org/pdf/1308.4644) の算術列の場合の接錐Betti一致による。前者の \(m=qV+b,\ 1\le b\le V\) に対して \(D=V-b+1\)。両一次資料で任意体性とこの適用を確認した。第一行は12.5で直接にも証明する。

第一行の混合語長にはSavchev–Chen, Long zero-free sequences in finite cyclic groups, [§4 Theorem 8](https://arxiv.org/html/math/0602568v1) を使う。巡回群の零和のない列の長さが群位数の半分を超えるとき、あるunit倍で正の代表値の総和を群位数未満にできる、という正確なstatementを用いる。以下の適用を除き、旧N4・ratio・graph/TU定理は入力にしない。

### 12.2 共通基礎：actual endpoint模型とKoszul移行

ここでは \(C=k[s,st^a,st^b,st^u]\)、\(E=k[x,v]\)、内部環 \(T=k[y,z]\) とする。仮定は12.1のものとし、次の局所F1–F8で模型・全競合・socle上界・全標数の移行を証明する。

#### F 1. 数値半群の次数付き単項式基底

\(\nu(h)\) を \(h\in\Gamma\) の最大分解長とする。最小生成元は全て正なので、この最大値は有限である。半群環の極大イデアルの \(n\) 乗は、\(\nu(h)\ge n\) となる \(t^h\) で張られる。従って接錐
\[
G=\operatorname{gr} k[[\Gamma]]
\]
の次数 \(n\) の基底は \(\nu(h)=n\) の \((t^h)^*\) である。異なる数値指数 \(h\) に一次関係はない。この記述は任意の体で同じである。

整数コアを
\[
C=k[s,st^a,st^b,st^u]
\]
とし、四生成元の次数を1とする。これは多項式環の部分環であり、その単項式基底は
\[
(n,B)\longleftrightarrow s^nt^B,
\qquad B\in n\{0,a,b,u\}
\]
である。一般の offset は \(B\) と書き、固定した内部 offset \(b\) と区別する。コアの単項式を
\[
\phi(s^nt^B)=(t^{nm+dB})^*\in G_n
\]
に送る。\(\nu(nm+dB)>n\) の場合、この右辺は0と読む。

\(x,y,z,v\) を実際の四生成元の初期形に送ることから、これは次数付き環準同型である。各 \(h\in\Gamma\) の最大長分解を選べば次数 \(\nu(h)\) のコア単項式が \((t^h)^*\) に写るので、\(\phi:C\twoheadrightarrow G\) は全射である。固定次数 \(n\) では異なる \(B\) は異なる \(nm+dB\) を与えるので、核はコアの単項式基底の部分集合で張られる。したがって核は単項式イデアルである。

この写像は最小分解長を使っていない。生存条件は一貫して **最大長が現在の次数と一致すること** である。

#### F 2. 端点座標と有限個の \(M_r\)

\(0\le r<u\)、\(\epsilon_r=[r>0]\) とする。任意のコア単項式は一意に
\[
B=r+uK,\qquad n=L+K+\epsilon_r,
\qquad L,K\ge0
\tag{2.1}
\]
と書ける。\(L\ge0\) は \(B\le nu\) から従う。\(x\) は \(L\) を1増し、\(v\) は \(K\) を1増す。

各 \(i,j\ge0\)、\(i+j\le u-1\) に対して
\[
B=ia+jb,\quad r=B\bmod u,\quad K=\lfloor B/u\rfloor,
\quad L=i+j-K-\epsilon_r
\tag{2.2}
\]
を作り、同じ \(r\) に属する \(x^Lv^K\) で生成する \(E\) の単項式イデアルを \(M_r\) とする。

この有限リストが全コアを尽くすことを示す。内部因子が \(u\) 個以上ある語について最初の \(u\) 因子を取り、空語を含む \(u+1\) 個の prefix offset を mod \(u\) で見る。二つは一致する。その間の非空語は長さ \(\ell\)、offset \(cu\) を持つ。各内部 offset は厳密に0と \(u\) の間なので
\[
1\le c\le\ell-1.
\]
この部分語はコア内で \(x^{\ell-c}v^c\) に等しい。従って内部因子数を厳密に減らせる。反復して内部因子数を \(u-1\) 以下にできるから、(2.2) が全 \(E\) 生成元を尽くす。

有限群 \(\mathbb Z/u\) で \(a,b\) が生成する部分群は gcd 条件により全体である。有限群では負のステップを同じステップの非負回数に換えられるため、非負内部語で全剰余へ達する。最短経路に頂点の重複はないので長さは \(u-1\) 以下である。従って全 \(M_r\ne0\)、かつ \(M_0=E\) である。

異なる \((r,L,K)\) は異なる \((n,B)\) を表すので、\(E\) 加群として
\[
C\simeq\bigoplus_{r=0}^{u-1}M_r[\epsilon_r,r].
\tag{2.3}
\]
これは一般に自由加群分解でも \(S\) 加群直和でもない。

\(r\ne0\) の各極小生成元は (2.2) のリストから選べるため
\[
L+K\le u-2.
\tag{2.4}
\]
\(r=0\) の極小生成元は \((0,0)\) だけである。従って
\[
H_x:=\max\{L:(L,K)\in\operatorname{Min}M_r\text{ for some }r\}
\le u-2.
\tag{2.5}
\]

#### F 3. competition と clamp の必要十分性

あるコア単項式 \((n,B)\) の数値指数に、長さ \(n+\delta\) の競合表示があることは
\[
nm+dB=(n+\delta)m+dB'
\]
と同値である。\(\gcd(m,d)=1\) から \(\delta=jd\)、\(B'=B-jm\) となり、長い競合は正確に
\[
(n,B)\longmapsto(n+jd,B-jm),\qquad j\ge1
\tag{3.1}
\]
で尽くされる。\(\gcd(m,u)=1\) は必要ない。

R39 と同じく、長い側の剰余を \(r\)、短い source 側の剰余を \(s\) とする。\(r+jm=s+cu\) と書き、長い側の点を \((L,K)\in M_r\) とする。短い側の座標は
\[
(L-jd-c+\epsilon_r-\epsilon_s,\ K+c).
\tag{3.2}
\]
長い側をその極小生成元 \((L,K)\) の上方閉集合全体へ動かすと、短い側で競合する点は正確に
\[
\left(\max\{0,L-jd-c+\epsilon_r-\epsilon_s\},\ K+c\right)
\tag{3.3}
\]
の上方閉集合となる。負の第一閾値の clamp は、短い側の座標も非負という条件を入れたものにすぎない。clamp が長い側の最小点そのものに対応しなくても、短い側の \(L\) を0にすると長い側の \(L\) がその極小点以上へ増えるため、競合表示は実在する。

各 \(s\) に対し、全 \(j\ge1\) と全 \(\operatorname{Min}M_r\) からの (3.3) で生成するイデアルを \(T_s\) とする。\(c\ge1\) は \(m>u\)、\(j\ge1\) から従うので、第二閾値は非負であり、第二座標の追加 clamp は不要である。

短い側がコアに属する条件を残す必要がある。したがって
\[
N_s=M_s\cap T_s,
\qquad G\simeq\bigoplus_{s=0}^{u-1}M_s/N_s[\epsilon_s,s]
\tag{3.4}
\]
が正確な actual \(E\) 加群模型である。\(M_s\ne E\) の場合があるので \(M_s\cap T_s\) を \(T_s\) へ置き換えてはいけない。

短い側 \(s\) を先に固定する R24 の表記では
\[
r=(s-jm)\bmod u,\qquad c=(jm+r-s)/u,
\]
となり、(3.3) は R24 の (10) において長さ増分 \(j\) を \(jd\) へ換えた式である。二つの原文は同じ competition を逆向きに添字付けしている。

#### F 4. 全 competition の証明付き停止式

\(jm=qu+t\)、\(0\le t<u\) と書く。\(r=0\)、\(s=0\)、そのほかの場合を分けると
\[
c-\epsilon_r+\epsilon_s\ge\lfloor jm/u\rfloor.
\tag{4.1}
\]
例えば \(t=0\) では \(s=r,c=q\) で等号、\(t>0,r+t=u\) では \(s=0,c=q+1\) で等号、残りの場合では左辺は \(q\) または \(q+1\) である。

(3.3) の第一閾値は従って
\[
\max\{0,L-jd-\lfloor jm/u\rfloor\}
\le\max\{0,H_x-2j\}
\tag{4.2}
\]
以下である。\(m>u,d\ge1\) を用いた。次を置く。
\[
J_0=\lfloor(u-2)/2\rfloor,
\qquad p=u/\gcd(m,u).
\tag{4.3}
\]
\(j>J_0\) なら全 generator の第一座標は0である。同じ短い剰余 \(s\) について \(j\) を \(j+p\) へ増すと長い剰余 \(r\) は変わらず、carry は
\[
c\longmapsto c+m/\gcd(m,u)
\]
へ増える。第一座標0の範囲では第二座標だけが増えるから、後の generator は前の generator の倍数となる。任意の \(j>J_0+p\) は \(J_0+1,\ldots,J_0+p\) のいずれかへ周期を減らせる。従って
\[
T_s=\sum_{j=1}^{J_0+p}T_{s,j},
\quad N_s=M_s\cap T_s
\tag{4.4}
\]
である。これは全 \(m,d\) で成立する停止式であり、数値実験に基づく打切りではない。

さらに \(B=d+\lfloor m/u\rfloor\) として
\[
J'_0=\max\{0,\lfloor(H_x-1)/B\rfloor\}
\]
を用いれば \(J'_0+p\) でも停止する。ただし実装には上の単純な (4.3) で十分である。

全剰余に長い側の極小点が存在し、\(j>J_0\) では第一座標が0になるので、各 \(T_s\) は純粋な \(v\) 冪を含む。また
\[
v^m=0\quad\text{in }G,
\]
なぜならその指数 \(m(m+du)\) は \(m+du\) 個の multiplicity generator で表せ、\(m+du>m\) だからである。従って \(v^mM_s\subset N_s\)、全 \(N_s\ne0\)、\(G\) は \(E\)-rank 0 である。

#### F 5. \(P,R\) の有限計数と端点 Koszul 長さ

\[
P=\sum_s\#\{g\in\operatorname{Min}M_s:g\notin N_s\},
\]
\[
R=\sum_s\#\{q\in M_s\setminus N_s:xq,vq\in N_s\}.
\tag{5.1}
\]
商 \(M_s/N_s\) の極小 \(E\) 生成元は、生存する \(M_s\) の極小生成元に正確に一致する。極小でない生存単項式を割る \(M_s\) の極小生成元は、もし \(N_s\) に入れば倍数も \(N_s\) に入るため、やはり生存するからである。

\(N_s\) の極小点を
\[
(a_0,b_0),\ldots,(a_t,b_t),\qquad
a_0<\cdots<a_t,\quad b_0>\cdots>b_t
\]
と並べる。\(E/N_s\) の両端点 socle の単項式基底は正確に
\[
(a_{i+1}-1,b_i-1),\qquad 0\le i<t
\tag{5.2}
\]
である。実際、これらはイデアルの下側で、\(x\) または \(v\) を1回掛けると隣り合う generator に入る。逆に両方で入る点は、\(x\) で入れる generator と \(v\) で入れる generator が隣接するこの形に限られる。負の座標の候補は存在せず、端の無限領域は両方で殺されない。従って (5.2) のうち \(M_s\) に属する点を数えれば \(R\) が得られる。

\(K(x,v;G)\) の \(H_0\) は \(Q_G=G/(x,v)G\) で長さ \(P\)、\(H_2\) は \((0:_G(x,v))\) で長さ \(R\) である。\(G\) は有限生成 \(E\) 加群であるからその最小自由解消は長さ2以下である。\(E\)-rank が0なので自由解消の rank の交代和から
\[
P-\dim_kH_1+R=0.
\]
従って
\[
\boxed{\dim_kH_\bullet(x,v;G)=(P,P+R,R).}
\tag{5.3}
\]
空の剰余成分も許す。ここで必要な標準代数事実は、二変数多項式環の Hilbert syzygy と、自由解消を分数体へテンソルした際の Euler 恒等式だけである。

#### F 6. actual socle の \(m,d\) 一様上界

内部ステップ \(a,b\) の mod \(u\) 最短語長を \(\ell_r\)、\(\ell_0=0\) とし、
\[
W=1+\sum_{r=0}^{u-1}\ell_r.
\]
最短語による点を \((L_r,K_r)\in M_r\) とすれば
\[
L_r+K_r=\ell_r-\epsilon_r.
\tag{6.1}
\]

まず \(P_C:=\sum_r\#\operatorname{Min}M_r\le W\) を証明する。\(r\ne0\) で、最短点は \(M_r\) の極小点である。もし他の点に厳密に支配されれば、座標和が減って内部語長も減るため最短性に反する。極小点を第一座標昇順に並べると、\((L_r,K_r)\) の左には第一座標の整数減少幅から高々 \(L_r\) 点、右には第二座標の整数減少幅から高々 \(K_r\) 点がある。従って極小点数は \(L_r+K_r+1=\ell_r\) 以下。\(M_0=E\) の1点を加えて
\[
P_C\le1+\sum_{r\ne0}\ell_r=W.
\tag{6.2}
\]

次に \(T_s\) の極小点を第一座標昇順に並べ、その点数を \(z_s+1\)、最小の第二座標を \(\kappa_s\) とする。純粋な \(v\) 冪が存在するので最初の第一座標は0である。任意の \((p,q)\in T_s\) に対し、それを割る極小点 \((A,B)\) を取る。その左には高々 \(A\) 点、右には高々 \(B-\kappa_s\) 点があるので
\[
z_s\le A+B-\kappa_s\le p+q-\kappa_s.
\tag{6.3}
\]
これは「全ての二変数単項式イデアルに無条件に成り立つ」補題ではなく、純 \(v\) 冪の存在を使っている。

任意の competition generator は第二座標 \(K+c\) を持ち、
\[
c=(r+jm-s)/u\ge\lceil(m-s)/u\rceil
\]
なので
\[
\kappa_s\ge\lceil(m-s)/u\rceil,
\qquad\sum_{s=0}^{u-1}\lceil(m-s)/u\rceil=m.
\tag{6.4}
\]
各 \(r\) の最短点に \(j=1\) を適用する。\(s=(r+m)\bmod u\) は \(r\) の置換であり、carry \(c_r=(r+m-s)/u\) の総和は \(m\) である。対応する (3.3) の第一座標は \(L_r\) 以下、第二座標は \(K_r+c_r\) だから (6.3) を足して
\[
\sum_s z_s\le\sum_r(L_r+K_r)+m-\sum_s\kappa_s
\le\sum_r(L_r+K_r)=W-u.
\tag{6.5}
\]
最後の等号は (6.1) と \(\sum_r\epsilon_r=u-1\) による。

自然写像 \(M_s/(M_s\cap T_s)\hookrightarrow E/T_s\) は単射である。従って前者の両端点 socle は後者の socle に入る。\(E/T_s\) の socle 次元は \(z_s\) なので
\[
R\le\sum_s z_s\le W-u.
\tag{6.6}
\]

(4.2) から全 competition generator の第一座標は \(\max(H_x-2,0)\) 以下である。単項式イデアルの極小生成元は generator リストから選ばれ、第一座標は互いに異なる整数で、0の点も存在する。従って \(z_s\le\max(H_x-2,0)\)。合わせて
\[
\boxed{R\le\widehat R:=\min\{W-u,\ u\max(H_x-2,0)\}.}
\tag{6.7}
\]
この証明に \(\gcd(m,u)=1\)、\(m,d\) の有限上限、Cohen–Macaulay 性は不要である。また \(P_C+R\le W\) は導かれないし、本稿では使用しない。

#### F 7. 二変数 Artin 商、\(\sigma\) の有限計算

\[
Q=C/(x,v)C.
\]
これは \(T=k[y,z]\) の標準次数付き Artin 商である。実際、コアの各剰余で \(x\) または \(v\) で割れる点は消え、残る基底はちょうど \(\operatorname{Min}M_r\) である。従って \(\dim_kQ=P_C\)。第2節の prefix 消去により次数 \(u\) 以上は全て0なので有限である。

剰余 \(r\) の極小点 \((L,K)\) に内部 offset \(\alpha\in\{a,b\}\) を掛ける。\(r+\alpha=s+cu\) とすれば移動先は
\[
\left(s,\ L+1+\epsilon_r-c-\epsilon_s,\ K+c\right).
\tag{7.1}
\]
この点が \(M_s\) の極小点なら対応する基底元へ写り、極小でなければ0へ写る。各固定乗法は \((n,B)\mapsto(n+1,B+\alpha)\) であるから、異なる基底元の非零像は異なる。従ってどの体でも、各乗法の核はその乗法で0へ写る基底元で張られる。特に
\[
\sigma:=\dim_k(0:_Q(y,z))
\]
は、(7.1) で \(y,z\) の双方が0になる基底点の個数である。整数だけで有限に計算でき、標数に依存しない。

\(T\) 上の極小生成元数は1、最終 Koszul homology は上記 socle なので最終 Betti 数は \(\sigma\) である。\(Q\) は有限長だから \(T\)-rank は0であり、二変数 Euler 恒等式から
\[
\boxed{\beta^T(Q)=(1,\sigma+1,\sigma).}
\tag{7.2}
\]
これは R25 の構造定理を要しない。使用するのは有限基底、二変数 Koszul 複体、rank の交代和のみである。

#### F 8. actual kernel を保持した \(S\)-Betti 上界

\(C\twoheadrightarrow G\) から実際の \(T\) 加群全射
\[
Q\twoheadrightarrow Q_G=G/(x,v)G
\]
が生じる。その核を \(K\) とする。\(\dim_kK=P_C-P\) である。Tor 長完全列から
\[
b_i^T(Q_G)\le b_i^T(Q)+b_{i-1}^T(K)
\le b_i^T(Q)+(P_C-P)\binom2{i-1}.
\tag{8.1}
\]
最後の不等式は \(K\) の Koszul 鎖群の次元による。商の Betti 単調性は仮定していない。

actual \(G\) 上の \(K(x,y,z,v;G)\) を、端点と内部の Koszul 二重複体に分ける。端点 homology を先に取る有限 spectral sequence は \(\operatorname{Tor}^S(G,k)\) に収束する。全 homology の長さは有限で、後の page は部分商なので total degree ごとの次元は増えない。第0行は正確に内部 Koszul homology \(\operatorname{Tor}^T(Q_G,k)\) とし、他の行を鎖群次元で評価すると、(5.3) より
\[
\beta_i^S(G)
\le b_i^T(Q_G)+(P+R)\binom2{i-1}+R\binom2{i-2}.
\tag{8.2}
\]
(8.1) を代入し Pascal 恒等式を使うと
\[
\boxed{\beta_i^S(G)\le b_i^T(Q)+P_C\binom2{i-1}
                         +R\binom3{i-1}.}
\tag{8.3}
\]
従って (7.2) から
\[
\boxed{\begin{aligned}
\beta_0^S(G)&=1,\\
\beta_1^S(G)&\le P_C+\sigma+1+R,\\
\beta_2^S(G)&\le2P_C+\sigma+3R,\\
\beta_3^S(G)&\le P_C+3R,\\
\beta_4^S(G)&\le R,\\
\beta_i^S(G)&=0\quad(i>4).
\end{aligned}}
\tag{8.4}
\]
右辺の \(R\) は (6.7) の \(\widehat R\) に置き換えてもよい。\(y,z\) は剰余成分を移すが、二重複体は actual \(G\) 上で定義されるため問題はない。

参考に第0行も鎖群次元だけで評価すると R24 の粗い上界
\[
(\beta_1,\beta_2,\beta_3,\beta_4)
\le(3P+R,\ 3P+3R,\ P+3R,\ R)
\]
も得られる。これは (8.4) と異なる評価であり、どちらの右辺も同じ source の実 \(P,R\) または \(P_C,\sigma,R\) に基づく。

### 12.3 非primitive枝：全域を紙上で比較する

#### NP 1. 結論と正確な仮定

任意体 `k`、整数

\[
0<a<b<u,\qquad \gcd(a,b,u)=\gcd(m,d)=1,\qquad d\ge2,
\qquad du\le m-2
\tag{H}
\]

を取る。
\(\Gamma=\langle m,m+da,m+db,m+du\rangle\) の接錐を `G`、
実interval completion
\(\widetilde\Gamma=\langle m,m+1,\ldots,m+du\rangle\) の接錐を
\(\widetilde G\) とする。双方をそれぞれの最小多項式表示で測ると

\[
\beta_i(G)\le\beta_i(\widetilde G)\quad(i\ge0)
\tag{C}
\]

が成り立つ。以下に有限campaignを使わない証明を記す。
唯一の特殊な公刊入力は実intervalのBetti公式（§7）であり、source側は
標準的なKoszul複体とスペクトル系列以外に旧定理を要しない。
`R25-K01` のgraph rank/TU、実第二微分の完全rank公式、
`R26-A01` の有限残余、Savchev–Chen、R21-N04、wide/ordinary枝は不要である。

`u>=3` は `0<a<b<u` から従う。(H)では全source生成元は `[m,2m-2]` に入るので
真の最小生成系であり、targetの全 `du+1` 個も最小である。
以下のsource構造は実は `d>=1,m>=1` で同じgcd条件と最小生成条件を課せば使える。

#### NP 2. 正規化された斉次環と二変数ideal

\[
C=k[s,st^a,st^b,st^u],\quad x=s,\quad y=st^a,\quad z=st^b,
\quad v=st^u,\quad E=k[x,v].
\]

内部語 `y^p z^q` について

\[
ap+bq=r+Ku,\quad0\le r<u,\quad
\epsilon_r=\boldsymbol1_{r>0},\quad L=p+q-K-\epsilon_r
\]

と置く。`K,L>=0` である。例えば `L>=0` は内部offsetが `u` 未満なので
\(\lceil(ap+bq)/u\rceil\le p+q\) から従う。
その語に対応する `x^L v^K` で生成される単項式idealを `M_r` とする。
`gcd(a,b,u)=1` により全剰余に内部語が存在する。
通常次数とoffsetを基底の添字として用いれば

\[
C=\bigoplus_{r=0}^{u-1}M_r[\epsilon_r,r],\qquad M_0=E.
\tag{1}
\]

各基底元 `(L,K,r)` の次数は `n=L+K+epsilon_r`、offsetは `r+Ku`。
異なる次数またはoffsetは `C` で線形独立なので(1)はexactである。

#### NP 3. 最小内部語の長さはu−2以下：外部零和定理は不要

内部語が非空の零和部分語を持ち、その長さが `h`、offset和が `ku` なら
`1<=k<=h-1` であり、その因子を `x^(h-k)v^k` へ置換できる。
この内部語はendpoint最小ではない。

両種類を含む長さ `u-1` の零和のない列が存在するとする。
任意の順序で、空prefixを含む全 `u` 個のprefix剰余は相異なり、
したがって全剰余を尽くす。隣接する異なる二項を交換するとちょうど一つの
prefix剰余だけが変わり、変更後の剰余は変更前と異なる。
残る `u-1` 個のprefix剰余のいずれかに一致するので、交換後に零和部分語が生じる。
零和部分語の有無は順序によらず、矛盾する。
よって両種類を含むendpoint最小語の長さは `u-2` 以下。
長さがさらに大きい混合語は長さ `u-1` の混合因子を取ればよい。

純 `y` 語について、`gcd(a,u)>1` なら長さ `u/gcd(a,u)<=u-1` の零和因子がある。
`gcd(a,u)=1` なら一意な `q` が
`qa=b mod u, 2<=q<=u-1` を満たす。
`qa=b+ku` の `k` は `0<=k<=q-1` であるから
`y^q=x^(q-1-k) z v^k`。右辺は正個数のendpointを含む。
純 `z` 語も同様である。

したがって全 `M_r` の最小generatorは長さ `u-2` 以下の内部語に由来し、
特に

\[
r>0\Longrightarrow L+K\le u-3;
\quad M_0\text{ の最小generatorは }1\text{ のみ}.
\tag{2}
\]

これは原文が `R26-A01 §3` に委ねた部分の独立な初等証明である。

#### NP 4. actual order競合はdずつ長さを増やす

`C` の基底元 `(L,K,r)` の実weightは

\[
nm+d(r+Ku),\qquad n=L+K+\epsilon_r.
\]

このweightの最大factorization長が `n` なら基底元をそのinitial formへ送り、
`n` より長ければ零へ送る。これが次数を保つ全射 `C->G` を与える。
同次数の異なるoffsetは異なるweightなので、kernelはこの基底について単項式である。

長さ `n+j` の競合表示があるならweightの一致から `d|jm`。
`gcd(m,d)=1` より必ず `j=d ell, ell>=1`。
そこで

\[
r_\ell=(r-\ell m)\bmod u,\quad
\kappa_{r,\ell}=(\ell m+r_\ell-r)/u
\tag{3}
\]

と置く。`ell*m=t*u+s, 0<=s<u` と書けば `kappa=t` または `t+1` なので

\[
\kappa_{r,\ell}\ge\lfloor\ell m/u\rfloor
\ge\ell\lfloor m/u\rfloor\ge0.
\tag{4}
\]

競合側の座標は

\[
K'=K-\kappa_{r,\ell},\qquad
L'=L+d\ell+\kappa_{r,\ell}+\epsilon_r-\epsilon_{r_\ell}.
\]

`x^l v^q` を `M_(r_ell)` の最小generatorとすると、その競合表示が存在する必要十分条件は

\[
K\ge q+\kappa_{r,\ell},\qquad
L\ge l-d\ell-\kappa_{r,\ell}+\epsilon_{r_\ell}-\epsilon_r.
\tag{5}
\]

従って、全 `ell>=1` と全最小generatorについて

\[
x^{\max(l-d\ell-\kappa_{r,\ell}+\epsilon_{r_\ell}-\epsilon_r,0)}
v^{q+\kappa_{r,\ell}}
\tag{6}
\]

で生成するidealを `T_r` とすれば、exactに

\[
G=\bigoplus_r M_r/(M_r\cap T_r)[\epsilon_r,r].
\tag{7}
\]

ここでは競合側が `C` で表示可能であることだけを調べる。
その競合側自身のinitial formが零でも、より長いfactorizationが存在する事実は変わらない。

参考として有限停止式も正しい：`ell>u` なら(2)より全x閾値は零。
`p=u/gcd(m,u)` とすると `r_(ell+p)=r_ell`、
`kappa_(ell+p)=kappa_ell+m/gcd(m,u)`。
`ell>u+p` の候補は `ell-p>u` の候補に支配されるため
`ell=1,...,u+p` だけで(7)を構成できる。
ただし以下の全称証明はこの有限構成を実行しない。

#### NP 5. P、R、sigmaの上界

\[
Q=G/(x,v)G,\quad P=\dim_k Q,\quad
R=\dim_k(0:_G(x,v)),\quad
\sigma=\dim_k(0:_Q(y,z)).
\]

`Q` は `k[y,z]` の単項式Artin商である。
実際、同じ通常次数と内部offsetを持つ二つの内部語の指数は
`a!=b` より一致する。従ってendpointを殺した後に内部語間の未処理二項同一視は残らず、
`C->G` の追加kernelも上記の単項式kernelである。
§3より全標準語の長さは `u-2` 以下なので

\[
P\le\#\{(p,q)\in\mathbb N^2:p+q\le u-2\}=\binom u2.
\tag{8}
\]

二変数の単項式Artin商のsocle語は固定されたy指数につき高々一つ。
y指数は `0,...,u-2` だから

\[
\sigma\le u-1.
\tag{9}
\]

`D=d+floor(m/u)` と置く。(2),(4)により(6)のx指数は
`r_ell>0` の場合

\[
\begin{cases}
\max(u-D-2,0),&r=0,\\
\max(u-D-3,0),&r>0
\end{cases}
\]

以下である。`r_ell=0` なら `l=q=0` なのでx指数は零である。
従って `T_r` の最小generatorの全x指数も同じ上界を満たす。

一般に、二変数単項式ideal `T` の最小generatorのx指数がすべて `H` 以下なら、
`E/T` の `(x,v)`-socleは高々 `H` 次元。
socle単項式 `x^i v^j` の条件 `x^(i+1)v^j in T` と `x^i v^j notin T` から
あるgeneratorのx指数は `i+1` であり、`0<=i<=H-1`。
固定した `i` についてsocleのv指数は高々一つなので主張が従う。
`E/T` がArtinであるとの仮定は不要である。

`M_r/(M_r cap T_r)` は `E/T_r` の部分加群なので、そのsocleも上記socleの部分空間。
これを(7)で足せば

\[
R\le R_0:=\max(u-D-2,0)+(u-1)\max(u-D-3,0)\le u^2.
\tag{10}
\]

最後の粗評価は各max項が `u` 以下であることだけで十分。

#### NP 6. 一般Koszul二重複体：実第二微分の完全rankは不要

`v^m=0 in G`。実際 `m(m+du)` は `m+du` 個の `m` でも表示でき、
`m+du>m` である。
`G` は有限生成 `E`-moduleで、`E`-rankは零。
`E` の二変数Koszul複体で `H_0=Q`、`H_2=(0:_G(x,v))` である。
有限自由分解のrank Euler式から

\[
\dim_k H_q(x,v;G)=(P,P+R,R)\quad(q=0,1,2).
\tag{11}
\]

全Koszul複体をendpoint `(x,v)` と内部 `(y,z)` に分ける。
endpoint homologyを先に取るスペクトル系列の次の頁は

\[
E^2_{p,q}=H_p(y,z;H_q(x,v;G))
\Longrightarrow H_{p+q}(x,y,z,v;G).
\tag{12}
\]

`q=0` 行は実際の `Q` の内部Koszul homologyである。
`Q` は二変数Artin商だから `H_0=k`、`H_2=socle(Q)`、Euler式より

\[
(\dim H_0(y,z;Q),\dim H_1(y,z;Q),\dim H_2(y,z;Q))
=(1,\sigma+1,\sigma).
\]

`q=1,2` 行はKoszul鎖群の次元で上から抑えるだけでよい。
スペクトル系列の各微分は全次数ごとの次元を増やさないため

\[
\beta_i(G)\le b_i(Q)+(P+R)\binom2{i-1}+R\binom2{i-2}.
\]

従って任意体上で

\[
\beta_1\le P+R+\sigma+1,\quad
\beta_2\le2P+3R+\sigma,\quad
\beta_3\le P+3R,\quad
\beta_4\le R.
\tag{13}
\]

実第二微分は(12)に含まれ、その値を零と置いたり変更したりしない。
その完全rankを算出せず(13)は成立する。
これにより原文の `c2>=P-sigma` の追加説明、graph/TU祖先を全て外せる。
(8)–(10)を代入すると

\[
(\beta_1,\beta_2,\beta_3,\beta_4)
\le\left(\frac{3u^2+u}2,\ 4u^2-1,\ \frac{7u^2-u}2,\ u^2\right).
\tag{14}
\]

#### NP 7. actual interval targetの全行支払い

(H)より有効幅は正確に `V=du`、特に `V>=2u`。
このtargetはtrue narrow intervalそのもので、ordinary semigroupには置換しない。
`b0=V-((m-1) mod V)` と置くと `1<=b0<=V`。
公刊arithmetic-sequence公式とそのtangent-cone一致から

\[
F_i:=\beta_i(\widetilde G)=i\binom V{i+1}+
\begin{cases}
(b_0+1-i)\binom V{i-1},&i\le b_0,\\
(i-b_0)\binom Vi,&i>b_0.
\end{cases}
\tag{15}
\]

正確な公刊入力：Herzog–Stamate,
*On the defining equations of the tangent cone of a numerical semigroup ring*,
arXiv:1308.4644v3, Proposition 2.5 (arithmetic-sequence ringと接錐の全Betti数一致)、
およびGimenez–Sengupta–Srinivasan, arXiv:1108.3203v1, Theorem 4.1
(任意体上のarithmetic-sequence商環の全Betti公式)。
Herzog–Stamate Theorem 2.6 は後者の再掲である。
添付原典の対応は `R01_LITERAL_PROOFS.md` L1015–1031。
同箇所は `m=qV+b,1<=b<=V` を用いており、`b0=V+1-b` とPascal恒等式で(15)になる。
両公刊一次資料でこの剰余変換と任意体の資格を確認した。

(15)の補正項は非負。第1行は補正が `b0>=1`、第2行は
`b0>=2` なら `(b0-1)V>=V`、`b0=1` なら `C(V,2)>=V` (`V>=6`) なので

\[
F_1\ge\binom V2+1,\quad
F_2\ge2\binom V3+V,\quad
F_i\ge i\binom V{i+1}\quad(i=3,4).
\tag{16}
\]

二項係数の上引数単調性により `V=2u` で(16)を評価すれば足りる。

* 第1行の余裕は
  \[\binom{2u}2+1-\frac{3u^2+u}2=\frac{(u-1)(u-2)}2>0.\]
* 第2行の余裕の3倍は
  \[8u^3-24u^2+10u+3
   =8z^3+48z^2+82z+33>0\quad(u=3+z,z\ge0).\]
* 第3行の余裕は
  \[3\binom{2u}4-\frac{7u^2-u}2
   =2u^4-6u^3+2u^2-u
   =2z^4+18z^3+56z^2+65z+15>0.\]
* 第4行について
  \[\frac{4\binom{2u}5}{u^2}
   =\frac1{15}\frac{2u-1}{u}(2u-2)(2u-3)(2u-4)
   \ge\frac1{15}\frac53\cdot4\cdot3\cdot2=\frac83>1.\]
  ここで各因子は `u>=3` で非減少である。

`i=0` は双方1、`i>4` は四変数sourceのKoszul複体が零。
これで(C)の全行が証明された。

### 12.4 Primitive枝の全高次行

#### H 1. Statement and one external target input

Let

\[
0<a<b<w<m,\qquad \gcd(a,b,w)=1,
\quad \Gamma=\langle m,m+a,m+b,m+w\rangle.
\]

Let \(k\) be any field, \(G=\operatorname{gr}k[[\Gamma]]\),
\(S=k[x,y,z,v]\), \(A=k[x,v]\), and \(B=k[y,z]\). All four
generators are minimal: they are distinct elements of \([m,2m)\).
Their gcd is 1. Write

\[
Q=G/(x,v)G,\quad P=\dim_kQ,\quad
R=\dim_k(0:_G(x,v)),\quad
\sigma=\dim_k(0:_Q(y,z)).
\]

The result is

\[
\beta_i^S(G)\le F_i(m,w)\qquad(i\ge2),
\tag{H}
\]

including the requested true-narrow subrange \(w\le m-2\).
Here \(F_i\) is the Betti number of the actual interval completion
\(\langle m,m+1,\ldots,m+w\rangle\), over its own \(w+1\)
variables. The only input about that target used in this note is its exact
arbitrary-field formula

\[
F_i=i\binom w{i+1}+
\begin{cases}
(D+1-i)\binom w{i-1},&i\le D,\\
(i-D)\binom wi,&i>D,
\end{cases}
\quad D=w-((m-1)\bmod w)\in\{1,\ldots,w\}.
\tag{T}
\]

This target input is checked against
Gimenez–Sengupta–Srinivasan, arXiv:1108.3203, Theorem 4.1 (arbitrary field),
and Herzog–Stamate, arXiv:1308.4644v3, Proposition 2.5 (the arithmetic
sequence ideal and its tangent-cone ideal have equal Betti numbers). All source statements, capacity lower bounds from (T), and the finite certificate are proved here.

#### H 2. Exact homogeneous-offset core and actual competition

Use the homogeneous offset semigroup algebra

\[
C=k[s,st^a,st^b,st^w].
\]

For a monomial \(s^dt^n\in C\), put \(r=n\bmod w\),
\(\epsilon_r=\mathbf1_{r>0}\), and write uniquely

\[
n=r+Kw,\quad d=L+K+\epsilon_r,\qquad L,K\ge0.
\]

Nonnegativity follows from \(0\le n\le dw\). Multiplication by
\(x=s\) and \(v=st^w\) increases respectively \(L\) and \(K\).
Let \(M_r\subset k[x,v]\) consist of the coordinate monomials occurring
in residue \(r\). Each \(M_r\) is an ideal and

\[
C\simeq\bigoplus_{r=0}^{w-1}M_r[\epsilon_r,r]
\tag{2.1}
\]

as an \(A\)-module. In particular \(M_0=A\). The gcd assumption
ensures every residue is reachable, so every \(M_r\ne0\).

For clarity, the map from this core to the actual tangent cone is not assumed
injective. If \(\nu(N)\) denotes the maximum decomposition length of
\(N\in\Gamma\), the graded surjection \(C\to G\) sends
\(s^dt^n\) to the degree-\(d\) class of \(t^{dm+n}\). Its image is
nonzero precisely when \(\nu(dm+n)=d\). In each fixed degree, distinct
offsets give distinct actual weights. Its kernel is consequently a monomial
ideal of \(C\).

Fix \(r\) and \(j\ge1\), and set

\[
r_j=(r-jm)\bmod w,\qquad
\kappa_{r,j}=(jm+r_j-r)/w.
\]

A monomial with coordinates \((L,K)\in M_r\) has a longer expression
of length \(d+j\) exactly when some minimal generator
\((u,q)\in\operatorname{Min}M_{r_j}\) satisfies

\[
K\ge q+\kappa_{r,j},\qquad
L\ge u-j-\kappa_{r,j}+\epsilon_{r_j}-\epsilon_r.
\tag{2.2}
\]

Indeed the longer expression has offset \(n-jm\), whose coordinates are
\(K'=K-\kappa\) and
\(L'=L+j+\kappa+\epsilon_r-\epsilon_{r_j}\). Membership in
\(M_{r_j}\) is equivalent to divisibility by one of its minimal generators.
Define

\[
T_r=\bigl(
x^{\max(0,u-j-\kappa_{r,j}+\epsilon_{r_j}-\epsilon_r)}
v^{q+\kappa_{r,j}}:
j\ge1,\ (u,q)\in\operatorname{Min}M_{r_j}
\bigr).
\]

Thus, without replacing any column by a free column,

\[
N_r=M_r\cap T_r,\qquad
G\simeq\bigoplus_r M_r/N_r[\epsilon_r,r]
\tag{2.3}
\]

as \(A\)-modules. Since \(m>w\), integrality and
\(jm+r_j-r> (j-1)w\) imply \(\kappa_{r,j}\ge j\).
This also proves the nonnegativity of every displayed \(v\)-exponent.
These arguments already work at \(m=w+1\); true narrow only needs
\(m\ge w+2\).

#### H 3. Every minimal internal word has length at most w-2

A nonempty zero-sum subword of internal offsets has length \(\ell\)
and offset \(qw\), with \(1\le q\le\ell-1\), because each letter
is strictly between 0 and \(w\). Replacing it by
\(x^{\ell-q}v^q\) preserves degree and offset and produces positive
endpoint factors. A word admitting such a subword cannot be a minimal
\(A\)-generator.

Consider a mixed word of length \(w-1\). Suppose its multiset has no
nonempty zero-sum submultiset in \(\mathbb Z/w\mathbb Z\). For any
ordering, the \(w\) prefixes, including the empty prefix, have pairwise
distinct residues, hence exhaust the group. Choose an ordering with two
different adjacent letters and interchange them. Exactly one intermediate
prefix changes, and its new residue differs from the old residue. The other
\(w-1\) residues have not changed, so the new prefix coincides with one
of them. This yields a zero-sum contiguous subword in the new ordering,
contradicting the assumption on the multiset. Therefore every mixed word
of length \(w-1\) is nonminimal.

For \(y^{w-1}\), if \(g=\gcd(a,w)>1\), the factor \(y^{w/g}\)
is already an endpoint word; its endpoint factors are both positive.
If \(\gcd(a,w)=1\), there is a unique \(q\in\{2,\ldots,w-1\}\)
with \(qa\equiv b\pmod w\). Write \(qa=b+hw\). Because
\(0<a,b<w\), necessarily \(0\le h\le q-1\). Then

\[
y^q=x^{q-1-h}zv^h
\]

in \(C\), with a positive total of \(q-1\) endpoint factors.
So \(y^{w-1}\) is nonminimal. Interchanging \(a,b\) proves the same
for \(z^{w-1}\). Any longer internal word has a length-\(w-1\)
factor and is also nonminimal.

Consequently the minimal generators of all \(M_r\) are represented
by internal words of length at most \(w-2\). For \(r>0\), their
coordinates obey

\[
L+K\le w-3;\qquad \operatorname{Min}M_0=\{(0,0)\}.
\tag{3.1}
\]

There cannot be a relation between two distinct pure internal words with
the same degree and offset: the equations
\(u+z=u'+z'\), \(au+bz=au'+bz'\), with \(a\ne b\), force
the exponent pairs to agree. Hence both \(C/(x,v)C\) and the further
quotient \(Q\) are monomial Artin quotients of \(k[y,z]\).
Every standard word of \(Q\) has degree at most \(w-2\), giving

\[
P\le\sum_{d=0}^{w-2}(d+1)=\binom w2.
\tag{3.2}
\]

Different socle words of a two-variable monomial quotient have different
\(y\)-exponents: if two had the same exponent, the smaller would divide
the larger and could not be killed by \(z\). These exponents belong to
\(\{0,\ldots,w-2\}\), so

\[
\sigma\le w-1.
\tag{3.3}
\]

This proves the original shortened-word step without invoking the
Savchev–Chen theorem needed elsewhere for the first row.

#### H 4. Common endpoint socle bound

For \(r=0\), the \(x\)-exponent in every generator defining \(T_r\)
is at most \(A_0=\max(w-4,0)\). If \(r_j=0\), the exponent is
zero. Otherwise (3.1) gives
\(u-j-\kappa+1\le w-3-2j+1\le w-4\).
For \(r>0\), terms with \(r_j=0\) again have exponent zero; the
other terms have exponent at most
\(w-3-2j\le w-5\). Thus their bound is
\(A_1=\max(w-5,0)\).

The inclusion \(M_r\hookrightarrow A\) induces

\[
M_r/(M_r\cap T_r)\hookrightarrow A/T_r.
\]

Its common \((x,v)\)-socle is a subspace of that of \(A/T_r\).
For a two-variable monomial ideal whose minimal generators have
\(x\)-exponents at most \(A\), each finite socle corner is between
two successive staircase generators. Its \(x\)-coordinate belongs to
\(\{0,\ldots,A-1\}\), and these coordinates are distinct. This
argument works even if the quotient is not Artinian. There are at most
\(A\) such corners. Summing the residue columns gives

\[
R\le \max(w-4,0)+(w-1)\max(w-5,0).
\tag{4.1}
\]

In particular \(R=0\) for \(w=3,4\), and for \(w\ge5\),

\[
R\le w^2-5w+1.
\tag{4.2}
\]

No socle is counted in an unrelated quotient, and no actual source top
Betti number is set to zero without the stated width restriction.

#### H 5. General double-complex bounds over every field

The \(A\)-module \(G\) is finitely generated by Section 3 and has
rank zero: \(v^m=0\) because the weight \(m(m+w)\) of that word
also has an expression of length \(m+w>m\). Its zeroth and second
\(A\)-Betti numbers are respectively \(P\) and \(R\), the latter
by the last homology of \(K(x,v;G)\). Euler characteristic of a
finite free \(A\)-resolution gives

\[
\beta^A(G)=(P,P+R,R).
\tag{5.1}
\]

Split the actual Koszul complex \(K(x,y,z,v;G)\) into the endpoint
and internal directions. On the page obtained by taking endpoint
homology, its row dimensions are
\(\beta^A_q(G)\binom2p\). On the next page, the row \(q=0\)
is exactly \(H_p(y,z;Q)\). Since \(Q\) is an Artin quotient
of \(B\), its \(B\)-Betti numbers are

\[
\beta^B(Q)=(1,\sigma+1,\sigma).
\tag{5.2}
\]

Here the last entry is the Koszul socle, the first is cyclicity, and
Euler characteristic gives the middle entry. The other two rows on that
page have dimensions at most their preceding-page dimensions. Every later
page can only decrease dimensions. Therefore

\[
\beta_i^S(G)\le
\beta_i^B(Q)+(P+R)\binom2{i-1}+R\binom2{i-2}.
\tag{5.3}
\]

The binomial coefficient is zero outside \(0,1,2\), and so is
\(\beta_i^B(Q)\) outside \(0,1,2\). In particular,

\[
\boxed{\beta_2\le2P+3R+\sigma,\quad
\beta_3\le P+3R,\quad \beta_4\le R.}
\tag{5.4}
\]

This is the full spectral-sequence argument, rather than an assumption
that the second differential vanishes. It needs no transferred endpoint
matrix. Each bound holds separately over the chosen arbitrary field.
The quantities \(P,R,\sigma\) are monomial basis counts, so they are
independent of the characteristic; the argument does not require all
\(S\)-Betti numbers themselves to be characteristic independent.

#### H 6. Exact capacity inequalities

For \(w\ge3\), formula (T) gives

\[
F_2\ge2\binom w3+w.
\tag{6.1}
\]

Indeed, if \(D\ge2\), the additional term is
\((D-1)w\ge w\). If \(D=1\), it is
\(\binom w2\ge w\). The minimum is attained at \(D=2\).
For \(w\ge5\), similarly

\[
F_3\ge3\binom w4+\binom w2.
\tag{6.2}
\]

For \(D\ge3\) the extra term is at least \(\binom w2\);
for \(D=2\) it is \(\binom w3\ge\binom w2\), because
\((w-2)/3\ge1\); for \(D=1\) it is even larger. Also
\(F_4\ge4\binom w5\) since the extra term is nonnegative.

For \(w\ge5\), (3.2), (3.3), and (4.2) give

\[
\beta_2\le4w^2-15w+2,\quad
\beta_3\le(7w^2-31w+6)/2,\quad
\beta_4\le w^2-5w+1.
\]

With \(u=w-11\), the second-row difference satisfies the exact identity

\[
3\left(2\binom w3+w-(4w^2-15w+2)\right)
=u^3+18u^2+83u+60>0\quad(u\ge0).
\tag{6.3}
\]

With \(u=w-5\), the third- and fourth-row differences satisfy

\[
8\left(3\binom w4+\binom w2-(7w^2-31w+6)/2\right)
=u^4+14u^3+47u^2+34u+96>0,
\tag{6.4}
\]

\[
30\left(4\binom w5-(w^2-5w+1)\right)
=u^5+15u^4+85u^3+195u^2+124u+90>0.
\tag{6.5}
\]

Their coefficients are independently recomputed by exact rational
polynomial arithmetic in the new checker, with no finite-grid inference.
For \(w=4\), \(R=0\) and \(P\le6\), so
\(\beta_3\le6<7=\min F_3\), and \(\beta_4=0\).
For \(w=3\), the only internal pair is \((a,b)=(1,2)\), so the
source is the target. For \(i>4\), source Betti numbers vanish by
the four-variable Koszul complex. Only \(\beta_2\), \(4\le w\le10\),
remains to be checked.

#### H 7. All-m stability and a genuine finite reduction

If \(m\ge w(w-2)\), then for every \(0\le r<w\) and \(j\ge1\),

\[
\kappa_{r,j}\ge j(w-2)\ge w-2.
\]

This follows by integrality from
\(jm+r_j-r\ge jw(w-2)-(w-1)\).
In the definition of \(T_r\), every \(x\)-exponent is consequently
zero: if \(r_j>0\), it is bounded above before truncation by
\((w-3)-1-(w-2)+1=-1\), and if \(r_j=0\) it is negative as well.
All \(v\)-exponents are at least \(w-2\). Thus

\[
T_r=(v^{t_r}),\qquad t_r\ge w-2.
\]

Every minimal generator of \(M_r\) has \(v\)-exponent at most
\(w-3\) by (3.1); the unique generator in residue zero has exponent
zero. None is forbidden. Moreover, if a monomial belongs to
\(M_r\cap(v^{t_r})\), any minimal \(M_r\)-generator dividing it
has smaller \(v\)-exponent, so the monomial belongs to \(vM_r\).
Consequently the kernel \(C\to G\) is contained in \(vC\), and

\[
Q\cong C/(x,v)C,\qquad
P=\sum_r\mu(M_r).
\]

Finally \(M_r/(M_r\cap(v^{t_r}))\) embeds in \(A/(v^{t_r})\), on
which multiplication by \(x\) is injective. Hence

\[
\boxed{m\ge w(w-2)\Longrightarrow
R=0,\quad Q\cong C/(x,v)C.}
\tag{7.1}
\]

The isomorphism is an isomorphism of internal \(B\)-algebras, so
\(\sigma\) is stable too. One core computation per offset pair pays
the whole tail; the target is compared to its minimum over all residues of
\(m\), not just the tail onset.

For completeness, the historical finite competition cutoff is also valid.
Set \(J_0=\lfloor(w-2)/2\rfloor\) and
\(p=w/\gcd(m,w)\). For \(j>J_0\), all \(x\)-thresholds are zero,
by (3.1) and \(\kappa\ge j\). Also
\(r_{j+p}=r_j\) and
\(\kappa_{r,j+p}=\kappa_{r,j}+m/\gcd(m,w)\).
So for such \(j\), the generators at \(j+p\) are divisible by the
corresponding generators at \(j\). Thus \(1\le j\le J_0+p\)
suffices to compute every competition ideal exactly. The new checker does
not rely on this cutoff: it uses the different actual-order cutoff in the
next section.

#### H 8. Independent actual-order computation and its stopping proof

The new executable `checks/n4/check_higher_rows.py` imports only Python's standard
library. It reads no historical checker or certificate. It reconstructs
\(P,R,\sigma\) directly from actual maximum orders, rather than from
(2.2) or the author's endpoint tables.

For each residue \(\rho\bmod m\), let \(b_\rho\) be the least
element of \(\langle a,b,w\rangle\) in that residue. Let
\(\ell_\rho\) be the shortest number of letters \(a,b,w\) expressing
\(b_\rho\). Lexicographic Dijkstra on the finite residue graph computes
these pairs exactly: all edge weights are positive and the gcd assumption
makes every vertex reachable. Put
\(T_\rho=b_\rho+m\ell_\rho\) and \(E=\max_\rho T_\rho\).

For every \(N\equiv\rho\pmod m\) with \(N\ge T_\rho\),

\[
\nu(N)=(N-b_\rho)/m.
\tag{8.1}
\]

To prove the upper bound, an expression of length \(d\) has offset
\(N-dm\in\langle a,b,w\rangle\), hence offset at least
\(b_\rho\). For the lower bound, use an expression of \(b_\rho\)
with \(\ell_\rho\) nonzero offsets and add the requisite number of
zero-offset multiplicity generators. This is possible exactly when
\((N-b_\rho)/m\ge\ell_\rho\). Below \(E\), elementary integer
dynamic programming in the four actual generators computes \(\nu\).
The checker verifies agreement of this DP and (8.1) at every finite overlap.
This proves that the implemented order function is exact on all integers.

For each internal word of degree \(d\le w-2\), with actual weight
\(N=u(m+a)+z(m+b)\), its class belongs to the standard basis of \(Q\)
exactly when

\[
\nu(N)=d,\quad
\nu(N-m)\ne d-1,\quad \nu(N-m-w)\ne d-1.
\]

The empty word is handled separately. One extra degree \(w-1\) is
examined as a regression of the proven word bound. Socle words are exactly
the standard exponent pairs with neither immediate successor standard.

The common endpoint socle is counted by scanning every actual weight
\(0\le N\le E\) for

\[
\nu(N)\ge0,\quad
\nu(N+m)>\nu(N)+1,\quad
\nu(N+m+w)>\nu(N)+1.
\tag{8.2}
\]

This scan is exhaustive: at \(N\ge T_\rho\), (8.1) gives
\(\nu(N+m)=\nu(N)+1\), so \(x\) is not zero there. Multiplication
by each generator sends a basis weight to a distinct basis weight or to
zero. Thus its kernel, and the common kernel, are spanned by the basis
weights tested in (8.2), in every characteristic. This directly counts
\(R\), without using historical jump-height or endpoint-socle code.

The tail core is separately enumerated by homogeneous degree and reachable
offsets in \(\{0,a,b,w\}\). It is also checked against the minimal
coordinate generators of the \(M_r\), and against the actual-order
invariants at the first stable multiplicity. These are consistency checks;
the all-tail claim rests on (7.1), rather than on matching sampled tails.

#### H 9. Coverage, results, and audit conclusion

For each \(w=4,\ldots,10\), enumerate every
\(1\le a<b\le w-1\) satisfying \(\gcd(a,b,w)=1\), and every
integer

\[
w+1\le m<w(w-2).
\]

The remaining multiplicities are precisely the stable tail (7.1). The
counts and independently recomputed maxima are:

| w | primitive pairs | finite m>w points | true-narrow points | max 2P+3R+sigma, including tails | min F2 | slack |
|---:|---:|---:|---:|---:|---:|---:|
|4|3|9|6|12|12|0|
|5|6|54|48|16|25|9|
|6|9|153|144|20|46|26|
|7|15|405|390|24|77|53|
|8|18|702|684|30|120|90|
|9|27|1431|1404|35|177|142|
|10|30|2070|2040|41|250|209|
|total|108|4824|4716||||

These pair counts also have a separate arithmetic check. For \(w>1\),
the number of ordered residue pairs \((a,b)\bmod w\) with
\(\gcd(a,b,w)=1\) is the Jordan totient
\(J_2(w)=w^2\prod_{p\mid w}(1-p^{-2})\). Among them, each of
\(a=0\), \(b=0\), and \(a=b\) removes \(\varphi(w)\) pairs;
these three subsets are disjoint within the primitive pairs. Dividing by
two for \(a<b\) gives \((J_2(w)-3\varphi(w))/2\), which evaluates
to the seven displayed pair counts. The number of multiplicities per pair
is \(w^2-3w-1\), independently reproducing every finite-point count.

There is one tail per primitive pair, hence 108 tails. The original 4,824
points include exactly 108 ordinary boundary points \(m=w+1\); omitting
those leaves exactly the requested 4,716 true-narrow points. This enlarged
finite campaign does not weaken any of the requested hypotheses.

On every finite point and every tail the new checker verifies
\(2P+3R+\sigma\le2\binom w3+w\). Thus (5.4) pays the remaining
second row. Sections 5–6 pay all other higher rows. This proves (H), with
the sole outside input (T) explicitly isolated.

The independent direct-order controls include
\((P,R,\sigma)=(5,0,2),(6,0,2),(37,7,2),(101,17,2)\) for the four
historical low-width and non-CM examples. In particular the new source
count retains actual nonzero common endpoint socles.

No mathematical defect was found in the R26-A01 higher-row reduction.
The qualification is computational proof with an explicit exhaustive finite
certificate, rather than a formal proof-assistant kernel result. The
finite reduction itself, all tail multiplicities, and characteristic
universality are justified before the integer enumeration is used.

### 12.5 Primitive枝の第一行：全m上界と有限offset補題

#### P 2. actual interval target の第一容量を直接導く

\(m>w\) なので、source の四元も target の \(m,m+1,\ldots,m+w\) も
\([m,2m)\) にあり、全て真正な最小生成元である。
\(\gcd(a,b,w)=1\) から source の生成系 gcd も 1。
target は同じ multiplicity \(m\) と物理幅 \(w\) の actual completion である。

target の斉次 core を

\[
C_w=k[s,st,\ldots,st^w]
\]

とし、fiber \((d,n)\) は通常次数 \(d\)、offset \(n\) を意味する。
この fiber は \(0\le n\le dw\) のとき一次元、そうでなければ零である。
なぜなら \(0,1,\ldots,w\) の \(d\) 個の和は区間 \([0,dw]\) を全て埋めるからである。

core ideal は二次交換で生成される。同じ和を保つ交換
\(X_iX_j\leftrightarrow X_{i'}X_{j'}\) により、一つの内部因子を除いて
端点因子 \(X_0,X_w\) だけの word に直せる：
内部の二因子の和が \(w\) 以下なら \(X_0X_{i+j}\)、
\(w\) 以上なら \(X_{i+j-w}X_w\) に置く。
したがって同じ次数・offset の全単項式は二次交換で連結する。
core の最小二次関係の個数は

\[
\dim k[X_0,\ldots,X_w]_2-\dim(C_w)_2
=\binom{w+2}{2}-(2w+1)=\binom w2.
\tag{T1}
\]

fiber \((d,n)\) の実 weight は \(dm+n\)。この word が接錐で零になることは、
長さ \(d+\ell\), \(\ell\ge1\) の表示があることと同値であり、
その offset は \(n-\ell m\) である。したがって零なら \(n\ge m\)。
逆に \(n\ge m\) なら \(0\le n-m\le dw-m<(d+1)w\) なので、
offset \(n-m\) を長さ \(d+1\) で表示できる。従って bad fiber は正確に \(n\ge m\)。

\(d_0=\lceil m/w\rceil\ge2\) と置く。この bad ideal の最小生成 fiber は正確に

\[
d=d_0,\qquad m\le n\le d_0w.
\tag{T2}
\]

実際、次数 \(d_0-1\) では最大 offset が \((d_0-1)w<m\) なので、
(T2) は既存の bad fiber と一次因子の積にならない。
\(d>d_0\) と \(m\le n\le dw\) に対しては

\[
\max(0,n-(d-1)w)\le i\le\min(w,n-m)
\]

を満たす整数 \(i\) が存在する：\((d-1)w\ge m\) と \(n\le dw\) がそれを保証する。
従って \((d,n)=(d-1,n-i)+(1,i)\) で、前の fiber は bad。
これを繰り返すと (T2) で生成される。

core の二次関係と (T2) の \(d_0w-m+1\) 本の monomial lift は接錐 ideal を生成する。
core の最小関係は全て次数 2 で、接錐 ideal には一次式がないので、その最小性は失われない。
追加 lift の最小性と独立性は \(\mathrm{bad}/(C_w)_+\mathrm{bad}\) の異なる fiber 基底から従う。
よって任意体上で

\[
F_1=\beta_1(G_{\widetilde\Gamma})
=\binom w2+d_0w-m+1
=\binom w2+w-((m-1)\bmod w)
\ge F_{\min}:=\binom w2+1.
\tag{T3}
\]

これにより、本稿では interval の外部 Betti 公式を前提にしない。

#### P 3. source core の二面支持と pure powers

\[
S=k[x,y,z,v],\qquad C=k[s,st^a,st^b,st^w],\qquad I_C=\ker(S\to C).
\]

通常次数 \(d\)、offset \(n\) を二重次数とする。
単項式を \((a\deg_y+b\deg_z,\ d,\ \mathrm{lex}_{y>z>x>v})\) で比較する。
これは乗法と両立する全順序で、第一重みが零の因子にも第二の正の通常次数があるので
well-order であり、1 が最小となる global monomial order である。
\(J_0=\operatorname{in}(I_C)\) とする。

core の各非零二重次数 fiber は一次元であるから、\(J_0\) の最小生成元 \(g\) に対し、
同じ次数・offset の標準単項式 \(h\) を取り \(g-h\in I_C\) とできる。
\(g,h\) に共通変数があれば、共通因子で割った binomial の先頭項が \(g\) を真に割るので
\(g\) の最小性に反する。従って \(g,h\) は互いに素である。

* \(v\mid g\) とすると \(v\nmid h\)。同じ offset を \(n\) としたとき、
  \(g\) の内部重みは \(n-w\deg_v(g)<n\)、\(h\) の内部重みは \(n\)。
  よって \(g\) は先頭項になれない。
* \(xyz\mid g\) とすると、相手 \(h\) は純 \(v\) 冪。
  同じ次数における平均 offset は \(g\) では \(w\) 未満、\(h\) では \(w\) なので不可能。
* \(xy\mid g\) かつ \(z\nmid g\) とすると、\(h\) は \(z,v\) のみを使う。
  平均 offset が左では高々 \(a\)、右では少なくとも \(b>a\) となり不可能。

従って

\[
\operatorname{Min}(J_0)\subset k[y,z]\ \cup\ k[x,z].
\tag{C1}
\]

特に \(J_0\) は \(v\) を含まず、正 \(x\) を持つ最小生成元には \(y\) がない。

\[
p=\min\left(\frac b{\gcd(a,b)},\frac w{\gcd(a,w)}\right),\qquad
q=\min\left(\frac{w-a}{\gcd(w-a,w-b)},\frac w{\gcd(b,w)}\right).
\tag{C2}
\]

\(g=\gcd(a,b)\) とした関係
\(y^{b/g}=x^{(b-a)/g}z^{a/g}\) は内部重みが等しく lex により左が先頭。
\(y^{w/\gcd(a,w)}\) と \(z^{w/\gcd(b,w)}\) の endpoint 零和関係では
内部重みの大きい純内部側が先頭。
また \(h=\gcd(w-a,w-b)\) とすると

\[
z^{(w-a)/h}=y^{(w-b)/h}v^{(b-a)/h}
\]

も左が内部重みの大きい先頭項である。従って \(y^p,z^q\in J_0\)。
最小純冪指数を \(p_0,q_0\) と書くと

\[
2\le p_0\le p\le b\le w-1,\qquad
2\le q_0\le q\le w-a\le w-1,
\tag{C3}
\]

\[
p_0\le\frac w{\gcd(a,w)},\qquad q_0\le\frac w{\gcd(b,w)}.
\tag{C4}
\]

下端が 2 であるのは、四つの一次 generator が異なる offset を持つため、一次関係がないからである。

#### P 4. 内部標準 word と endpoint 表示

\[
D=\{(s,t)\in\mathbb N^2:y^sz^t\notin J_0\},\quad
B=|D|,\quad K_0=\mu(J_0),
\]

\[
\phi(s,t)=(w-a)s+(w-b)t,\qquad M=\max_{D}\phi(s,t).
\tag{C5}
\]

\(D\) は、「同じ次数・offset に端点 \(x\) または \(v\) を含む表示がない」内部 word の集合と正確に一致する。
これを旧 endpoint 模型に頼らず証明する。

内部 word \(g=y^sz^t\) に endpoint 表示 \(h=x^Ay^uz^rv^K\) があるとする。
\(K>0\) なら \(h\) の内部重みが小さいので \(g\in J_0\)。
\(K=0,A>0\) なら、次数と offset の等式から

\[
(s-u)+(t-r)=A>0,\qquad a(s-u)+b(t-r)=0,
\]

従って \(s-u=bA/(b-a)>0\)。lex によりやはり \(g\) が先頭。
逆に内部 word が非標準なら、同じ次数・offset の異なる純内部 word は存在しない
（二本の一次方程式と \(a\ne b\) により一意）ので、その標準形は endpoint を含む。
これで同値が示された。また \(D\) は \(C/(x,v)C\) の単項式基底でもある。

#### P 5. 混合 word 長と無界幅に用いる三つの評価

\((s,t)\in D\), \(s,t>0\) とする。\(s\) 個の \(a\)、\(t\) 個の \(b\) を
\(\mathbb Z/w\mathbb Z\) の列とみなす。
非空零和部分列の長さを \(d\)、通常の整数和を \(Kw\) とすると、各 offset が \(0,w\) の間なので
\(1\le K\le d-1\)。対応因子を \(x^{d-K}v^K\) に直せて endpoint 表示を与える。
§4 に反するので、この列は零和のない列である。

\(s+t>w/2\) と仮定し Savchev–Chen を適用する。
unit 倍後の二種類の positive representative が両方 2 以上なら総和は
\(2(s+t)>w\) となる。従って一方は 1、他方は \(c\ge2\)。
元の offset を順に \(\alpha,\beta\)、その個数を \(R,T\ge1\) とする。
unit 性から \(c\alpha-\beta\) は \(w\) の倍数なので

\[
c\alpha=\beta+kw.
\]

ここで \(c\alpha-\beta>-w\) と \(c\alpha-\beta<cw\) より
\(0\le k\le c-1\)。従って core の関係

\[
Y_\alpha^c=x^{c-1-k}Y_\beta v^k
\tag{C6}
\]

は非負指数を持ち、右に endpoint 因子が合計 \(c-1>0\) 個ある。
\(D\) の意味から \(R<c\)。Savchev–Chen の総和は整数であるから \(R+cT\le w-1\)。
よって

\[
2(R+T)=(R+cT)+(R-(c-2)T)
\le(w-1)+(c-1-(c-2))=w,
\]

仮定と矛盾する。従って

\[
\boxed{(s,t)\in D,\ st>0\Longrightarrow s+t\le h:=\lfloor w/2\rfloor.}
\tag{C7}
\]

pure word は (C3) より長さ高々 \(w-2\)。混合 word は (C7) より
\(\lfloor w/2\rfloor\le w-2\)（\(w\ge3\)）。したがって **旧 R26 の内部長補題を使わず**

\[
s+t\le w-2\quad((s,t)\in D),\qquad M\le(w-2)(w-1).
\tag{C8}
\]

混合 word は \(s,t\ge1,s+t\le h\) の格子点なので高々 \(\binom h2\) 個。
軸上は単位元を一度だけ数えて \(p_0+q_0-1\) 個。よって

\[
B\le\binom h2+p_0+q_0-1
\le\frac{w^2}{8}+\frac{7w}{4}-3.
\tag{C9}
\]

また \(yz\) 面の最小生成元は \(z\) 指数が \(0,\ldots,q_0\) の各値に高々一つ、
正 \(x\) の最小生成元は \(z\) 指数が \(1,\ldots,q_0-1\) の各値に高々一つ。
各々同じ \(z\) 指数なら他方が可除になるからである。従って

\[
K_0\le(q_0+1)+(q_0-1)=2q_0\le2w-2.
\tag{C10}
\]

#### P 6. actual 接錐の初期 ideal と共通因子禁止

\(\nu(n)\) を \(n\in\Gamma\) の実最大表示長とする。
core fiber \((d,n)\) の実 weight は \(dm+n\) であり、その接錐への像が非零であることは
\(\nu(dm+n)=d\) と同値。\(\nu(dm+n)>d\) の core 単項式を bad と呼ぶ。
同じ次数の異なる offset は異なる実 weight を持つので、非零像は線形独立。
したがって \(C\to G\) の kernel は正確に bad fiber からなる monomial ideal である。

\(I_G=\ker(S\to G)\), \(J_*=\operatorname{in}(I_G)\) とすると、
\(J_*\) は \(J_0\) と bad な core 標準単項式を合わせた monomial ideal である。
これは同じ次数・offset の全単項式が core で同じ fiber に落ち、その fiber 全体が
接錐で非零か零かの二択であることから直ちに従う。

非core の最小生成元 \(g\in\operatorname{Min}(J_*)\setminus J_0\) は core 標準で bad。
\(g\) と同じ実 weight を持ち次数が \(\ell\ge1\) だけ大きい単項式 \(h\) を取る。
**任意のこのような長い表示 \(h\) は \(g\) と互いに素である。**
共通変数で割ると \(g\) の真の divisor が同じ正の次数差を持つ長い表示を得て bad となり、
\(g\) の \(J_*\)-最小性に反するためである。

正 \(x\) の \(g\) が \(y,z\) を共に含む場合、\(v\nmid g\) なら長い相手は純 \(v\) 冪、
\(v\mid g\) なら相手に使える変数がない。後者は明らかに不可能。
前者も、\(g\) の全数値因子は \(m+w\) 未満なのに、長い純 \(v\) 冪はそれより多い個数の
最大数値生成元を持つので同じ実 weight になれない。
従って正 \(x\) を含む bad 最小生成元では \(y,z\) の少なくとも一方がない。

#### P 7. 五支持の全数と全 multiplicity を消した \(U\)

次を定義する。

\[
A_0=\max\left(0,\left\lfloor\frac{M-2w-1}{w}\right\rfloor\right),
\tag{U1}
\]

\[
L_y=\sum_{r=1}^{p_0-1}\max\left(0,
\left\lfloor\frac{r(w-a)-2w+b}{2w+1}\right\rfloor\right),
\]

\[
L_z=\sum_{r=1}^{q_0-1}\max\left(0,
\left\lfloor\frac{r(w-b)-2w+a}{2w+1}\right\rfloor\right).
\tag{U2}
\]

いずれも \(a,b,w\) だけの量である。

##### I. \(x\) を含まない支持：高々 \(B\)

\(g=y^sz^tv^K\) と書く。\(J_0\) が \(v\) を含まないので \((s,t)\in D\)。
固定した \((s,t)\) で異なる \(K\) があれば一方が他方を割るため、最小生成元は高々一つ。
\((s,t)=(0,0)\) の純 \(v\) 冪も、この費用 \(B\) に含む。

##### II. 正 \(x\), \(v=0\)：高々 \(q_0-1\)

純 \(x\) 冪は同 weight の長い表示を持てない（各数値生成元が少なくとも \(m\)）。
\(xy\) 支持では相手は \(z,v\) のみを使い、相手の全数値生成元は source 因子より大きく、
個数も多いので不可能。§6 の排除と合わせ、残るのは
\(g=x^Az^t,A,t\ge1,t<q_0\)。固定 \(t\) に最小 \(A\) は高々一つ。

##### III. \(xv\) 支持：高々 \(A_0\)

\(g=x^Av^K,A,K\ge1\)。長い相手は共通因子禁止により純内部 word。
core 標準化が endpoint を導入すれば共通因子を持つ別の長い表示となるので、
相手は \(y^sz^t,(s,t)\in D\) と取れて、実際その範囲を外れられない。
次数差が \(\ell\) なら、次数・実 weight 等式より

\[
wA=\phi(s,t)-\ell(m+w)\le M-2w-1,
\tag{U3}
\]

最後は \(m>w\) と \(\ell\ge1\)。固定した正 \(A\) では最小の \(K\) は高々一つだから費用は (U1)。
(C8) より、\(w\ge5\) では

\[
A_0\le\max\left(0,\left\lfloor\frac{w^2-5w+1}{w}\right\rfloor\right)=w-5.
\tag{U4}
\]

##### IV. \(xyv\) 支持：高々 \(L_z\)

\(g=x^Ay^sv^K,A,s,K\ge1\)。長い相手は \(z^r\) のみ。
\(r\ge q_0\) なら \(z^{q_0}\) の core 関係を代入し、同じ次数・offset の別表示が
\(x,y,v\) の少なくとも一つを含む。この表示はなお長く、\(g\) と共通因子を持つため矛盾。
従って \(1\le r<q_0\)。また \(g\) 自身が core 標準なので \(1\le s<p_0\)。

\[
r=A+s+K+\ell,\qquad \ell m=as+wK-rb,
\]

\[
as\equiv rb+\ell m\pmod w.
\tag{U5}
\]

固定 \((r,\ell)\) に対し、(U5) の整数解が存在するなら、その \(s\) の間隔は
\(w/\gcd(a,w)\)。区間 \(1\le s<p_0\le w/\gcd(a,w)\) には高々一解しかない。
\(s\) が決まれば実 weight 式で \(K\)、次数式で \(A\) も一意となる。
したがって各 \(g\) に長い表示を一つ選ぶと \(g\mapsto(r,\ell)\) は単射である。
原 offset が 1 であることも、合同式に全剰余で一意解があることも仮定していない。

さらに

\[
\ell(m+w)=r(w-b)-wA-s(w-a)
\le r(w-b)-2w+a.
\]

\(m+w\ge2w+1\) なので、固定 \(r\) で取り得る正 \(\ell\) の個数は
(U2) の \(L_z\) の対応する summand 以下である。

##### V. \(xzv\) 支持：高々 \(L_y\)

\(g=x^Az^tv^K,A,t,K\ge1\)。相手は純 \(y^r\) で、同じ core 代入論証により
\(1\le r<p_0\)。\(g\) の標準性より \(1\le t<q_0\)。合同式は

\[
bt\equiv ra+\ell m\pmod w.
\]

解の間隔 \(w/\gcd(b,w)\) と (C4) から \((r,\ell)\) への単射。
また

\[
\ell(m+w)=r(w-a)-wA-t(w-b)\le r(w-a)-2w+b,
\]

なので費用は \(L_y\) 以下となる。

以上の五つは互いに重ならず、§6 と純 \(x\)、\(xy\) の排除により非core 最小生成元を尽くす。
どちらの三変数支持も捨てていないし、反射 source に移して費用を流用してもいない。
従って同じ actual source に対し

\[
\mu(J_*)\le U(a,b,w):=K_0+B+(q_0-1)+A_0+L_y+L_z.
\tag{U6}
\]

最後に \(\beta_1^S(G)=\mu(I_G)\le\mu(J_*)\)。
この不等式に高次 Betti の退化定理は要らない。
各最小単項式生成元を先頭項に持つ \(I_G\) の式を一つずつ取れば、それらは Gröbner basis で、
通常の除法により \(I_G\) を生成するからである。どの体でも同じ議論が通る。
よって

\[
\boxed{\beta_1(G)\le U(a,b,w)\quad\text{for every }m>w.}
\tag{U7}
\]

ここで初めて \(m\) が完全に除去される。後の有限 offset 計算の論理的前提は (U7) である。

#### P 8. \(w\ge48\) の無限定理

(U2) の各零切り上げ・床・負の項を落とし、非負の上界で評価すると

\[
L_y+L_z\le\frac{(w-a)p_0^2+(w-b)q_0^2}{4w}
\le\frac{(w-a)b^2+(w-b)(w-a)^2}{4w}\le\frac{w^2}{4}.
\tag{W1}
\]

最初の評価は \(\sum_{r=1}^{p_0-1}r=p_0(p_0-1)/2\) と \(2w+1>2w\) による。
最後を確認するには \(A=w-a\le w,B=b\le w\) として

\[
AB^2+(w-B)A^2\le w[B^2+w(w-B)]\le w^3,
\]

最後は \(B^2\le wB\) である。
(C9),(C10),(U4), \(q_0-1\le w-2\), (W1) を足すと、\(w\ge5\) に対して

\[
U\le\frac{3w^2}{8}+\frac{23w}{4}-12.
\tag{W2}
\]

actual target の最小容量 (T3) との差は

\[
F_{\min}-\left(\frac{3w^2}{8}+\frac{23w}{4}-12\right)
=\frac{w^2-50w+104}{8}.
\]

\(w=48+z,z\ge0\) と書くと分子は \(z^2+46z+8>0\)。したがって全 \(w\ge48\)、
全 \(a,b,m\) に第一行比較が成立する。有限幅や有限 multiplicity からの外挿ではない。

#### P 9. 残る有限領域を別アルゴリズムで完全評価する

残る入力は正確に

\[
3\le w\le47,\quad1\le a<b\le w-1,\quad\gcd(a,b,w)=1.
\tag{F1}
\]

`checks/n4/independent_offset_audit.py` は標準ライブラリだけを使い、著者コードや旧出力を入力にしない。
特に 旧合同候補リストを実装していない。
offset の一変数最短 word 問題から初期 ideal を直接復元する。

##### 9.1 direct-fiber アルゴリズムの完全性

\(L(n)\) を、offset \(n\) を \(a,b,w\) で表示する最短個数とする（不可能なら \(\infty\)）。
\(L(0)=0\) と漸化式

\[
L(n)=1+\min\{L(n-a),L(n-b),L(n-w)\}
\tag{F2}
\]

（負の添字を除く）で厳密に求める。これは \(n\) に関する帰納法で完全。
正 \(v\) を一個以上持つ表示の最短長は

\[
E(n)=\begin{cases}1+L(n-w)&n\ge w,\\\infty&n<w.\end{cases}
\tag{F3}
\]

純内部 \(y^sz^t\), \(d=s+t,n=as+bt\) に対し

\[
y^sz^t\in J_0\quad\Longleftrightarrow\quad L(n)<d\ \text{or}\ E(n)\le d.
\tag{F4}
\]

左向き：前者は余った次数を \(x\) で埋める endpoint 表示、後者は \(v\) を持つ表示。
右向き：§4 による endpoint 表示は、\(x>0\) で \(v=0\) なら offset 表示長が \(d\) 未満、
\(v>0\) なら \(E(n)\le d\)。

一方、\(x^Xz^t\) は \(n=bt,d=X+t\) を持つ。
\(v\) を使わない別表示がある場合、それは正 \(y\) を含み、lex で元の word より大きい。
したがって元より小さい表示があることは正 \(v\) 表示があることと同値であり

\[
x^Xz^t\in J_0\quad\Longleftrightarrow\quad X+t\ge E(bt).
\tag{F5}
\]

\(E(bt)<\infty\) のとき閾値は \(X=\max(0,E(bt)-t)\)。
これが direct-fiber core 構成である。

有限化は (C1)–(C3) により正当化される。
\(yz\) 面の最小生成元は \(0\le s\le p,0\le t\le q\) 内にあり、(F4) で全件判定できる。
正 \(x\) の最小生成元は \(1\le t<q_0\le q\) にあり、各 \(t\) で (F5) の閾値を一つ追加すれば十分。
可除な候補を除いて得られるものは、従って正確に \(\operatorname{Min}(J_0)\)。
DP が必要とする \(n\) は高々 \(ap+bq\) であり、これを超える不明な fiber は参照しない。
\(D\) 自体も \(0\le s<p,0\le t<q\) に対する (F4) で直接計算する。

これにより各 offset において \(K_0,p_0,q_0,D,B,M,A_0,L_y,L_z,U\) を厳密整数で得る。
core の最小生成元から得た membership と (F4) の全箱内 membership が一致することも毎回検査する。
符号付き rank や数値近似は使わない。

##### 9.2 全領域・出力

幅ごとの入力個数はループ結果に加えて、独立に Möbius 反転

\[
N(w)=\sum_{d\mid w}\mu(d)\binom{w/d-1}{2}
\tag{F6}
\]

でも照合した。\(a,b,w\) が共通 divisor \(d\) を持つ組の個数が
\(\binom{w/d-1}{2}\) であることから (F6) が従う。
\(\sum_{w=3}^{47}N(w)=13921\)。

全証書は `certificates/n4/independent_offset_certificate.json.gz`、概要は
`certificates/n4/independent_offset_summary.json`。証書内 payload の canonical JSON の SHA-256 は

`43d50ab43a88bee6648312b10e7a8c539edce06ccf938768ba64fa26bcdaf0ef`。

全組で (C3),(C7)–(C10),(W1) の整数版、正確な core membership を計算し、
\(U>F_{\min}\) は正確に

\[
\boxed{(a,b,w)=(1,w-1,w),\quad3\le w\le10.}
\tag{F7}
\]

となった。幅別最小 slack \(F_{\min}-U\) は以下。

|\(w\)|個数|最小 slack|\(w\)|個数|最小 slack|\(w\)|個数|最小 slack|
|---:|---:|---:|---:|---:|---:|---:|---:|---:|
|3|1|-3|18|99|27|33|450|168|
|4|3|-4|19|153|33|34|408|182|
|5|6|-4|20|132|40|35|540|196|
|6|9|-5|21|174|46|36|414|210|
|7|15|-5|22|165|54|37|630|225|
|8|18|-4|23|231|62|38|513|241|
|9|27|-4|24|180|70|39|636|256|
|10|30|-2|25|270|79|40|552|273|
|11|45|0|26|234|89|41|780|290|
|12|42|2|27|297|98|42|558|307|
|13|66|5|28|270|109|43|861|325|
|14|63|9|29|378|120|44|690|344|
|15|84|12|30|276|131|45|828|362|
|16|84|17|31|435|143|46|759|382|
|17|120|22|32|360|156|47|1035|402|

新計算の完了後、原著者出力の全 13,921 行とも比較し、core 最小生成元、pure caps、
\(B,M,A_0,L_y,L_z,U\)、容量、slack が全件一致した。
この後比較は独立計算の入力ではなく、二実装の相互検査である。

再実行：

```bash
python3 -B checks/n4/independent_offset_audit.py > /tmp/n4_offset_summary.json
```

全 \(m>w\) の理論上界 (U7) を評価した有限残余なので、有限 \(m\) grid の全称への外挿はない。

### 12.6 第一行の例外族を全mで直接処理する

12.5の例外は \((a,b,u)=(1,u-1,u),3\le u\le10\) だけである。この小節では \(u=w=t+1\)、\(m\ge w+2\)、\(S=k[x,y,z,v]\) と書き直す。\(w=3\) はsourceとtargetが同一なので終了。以下は第一行だけを扱い、高次行は12.4を使う。

まず、この族の全core初期idealとactual競合を明示する。局所B2–B3の \(J\) は \(\operatorname{in}(I_G)\)、従ってどの体でも \(\beta_1(G)\le\mu(J)\) である。

#### B 2. 明示 offset Gröbner basis

w=t+1 と置く。w=3 は source=target なので、以下 t>=3 としてよい。
S=k[x,y,z,v], A=k[x,v]、変数の offset をそれぞれ 0,1,t,t+1 とする。
offset 環

\[
C=k[s,sU,sU^t,sU^{t+1}]
\]

の kernel には次の t+1 個が入る。

\[
y^t-x^{t-1}z,\quad yz-xv,\quad
x^{t-q}z^q-y^{t+1-q}v^{q-1}\quad(2\le q\le t). \tag{3}
\]

内部重み wt(y)=1, wt(z)=t-1, wt(x)=wt(v)=0 を先に比較し、
通常次数、任意の lex 順を続ける global monomial order を使う。
(3) の左項は右項より内部重みが大きい。候補先頭 ideal は

\[
J_0=(y^t,yz,x^{t-q}z^q:2\le q\le t). \tag{4}
\]

標準単項式は次の 2t-1 列である。

* 自由列 1,y,...,y^(t-1),z：係数環 A。
* 制限列 z^q, 2<=q<=t-1：係数環 A/(x^(t-q))。

これらの像の (degree,offset) は相異なる。実際、自由列の offset 剰余は
0,1,...,t で一意である。制限列 z^q の剰余は r=t+1-q であり、
offset tq+K(t+1) は自由列 y^r v^(K+q-1) とだけ一致し得る。
後者の最小次数は t+K、前者の次数は q+K+L<t+K なので一致しない。
異なる制限列同士も剰余が異なる。同じ列の L,K は (degree,offset) から一意。

したがって (3) による停止する除算の標準余りは C で線形独立であり、
(3) は完全 Gröbner basis、(4) は actual initial ideal である。
これは Hilbert series の一致だけによる議論ではない。

#### B 3. actual tangent cone の全競合と initial ideal

列基点 b の次数を c、offset を n と書く。標準単項式 x^L v^K b の実半群 weight は
(L+K+c)m+n+K(t+1)。この monomial が G で消える必要十分条件は、
ある j>=1 に対し、同じ weight が次数 L+K+c+j で表示できることである。

w=t+1 とし

\[
r_j=(n-jm)\bmod w\in[0,t],\quad
\kappa_j=(jm+r_j-n)/w,
\]
\[
a(r)=\begin{cases}r,&0\le r<t,\\1,&r=t,\end{cases}
\qquad \Delta_j=a(r_j)-c-\kappa_j-j.
\]

自由 anchor は y^r (r<t) または z (r=t) であるから、その競合条件は厳密に

\[
K\ge\kappa_j,\qquad L\ge\Delta_j. \tag{5}
\]

2<=r_j<t のときは短い anchor
z^(w-r_j) v^(K-kappa_j-(t-r_j)) もあり、条件は

\[
K\ge\kappa_j+t-r_j,\qquad
L\ge\Delta_j-(r_j-1). \tag{6}
\]

これらは十分条件だけでなく必要条件でもある。第2節の全標準列を、指定した offset に
おいて分類すると自由 anchor とこの一つの制限 anchor しかなく、
制限 anchor の x 指数が制限を超えた領域は自由 anchor が既に覆うからである。

(5),(6) の各閾値を0で切り上げた x,v 単項式で生成する ideal を I_b とする。
制限列には既存の x^(t-q) 制限を加える。すると

\[
J=J_0+\sum_b bI_b=\operatorname{in}(I_G). \tag{7}
\]

証明：J_0 の標準 monomial を比較すると、非禁止 monomial は最大 order がその次数に等しく、
同次数では相異なる実 weight を持つ。これは G の実半群基底である。
各禁止 monomial は G で0。よって (3) による除算後、kernel の非禁止余りは線形独立性で0となり、
逆包含も得られる。

ここで M=t(t-1)、phi_b=wc-n>=0 と置くと

\[
w\Delta_j=(wa(r_j)-r_j)-\phi_b-j(m+w),
\qquad wa(r)-r\le M. \tag{8}
\]

短い anchor の対応する反射値は w-r<w なので、(6) の x 閾値は常に負である。
正の x 閾値は j< M/(m+w)、従って

\[
j\le J_{\max}=\lfloor(M-1)/(m+w)\rfloor \tag{9}
\]

にしか現れない。I_b は必ず純 v 冪を含む：v^m の実 weight は x^(m+w) のそれに等しく、
後者は w だけ長いからである。したがって各 I_b は、純 v 冪一つと正の x 閾値群で生成される。

独立 checker の有限 competitor 範囲の正当化も記す。
p=w/gcd(m,w) とすると j->j+p で r は同じ、kappa は m/gcd(m,w) 増加し、
Delta は p+m/gcd(m,w) 減少する。j>J_max の通常閾値は全て純 v 冪であり、
短い anchor の v 閾値はそれより大きい。よって全競合は 1<=j<=J_max+p で尽くされる。

#### B4 幅4と5の第一行

\(t=3,4\) では \(M=t(t-1)\)、\(m+w\ge M\) なのでB3の正の \(x\) 閾値は存在しない。\(n_b\) を列のoffsetとし
\[
\theta_n=\max\{\lceil(m-n)/w\rceil,0\}
\]
と置く。自由anchorの \(j=1\) が最小の純 \(v\) 閾値を与え、短いanchorはこれを下げないので、exactに
\[
J=J_0+(b v^{\theta_{n_b}}: b\text{ は全標準列}).\tag{B4}
\]

\(w=4,m=6\) では \(J=(v^2,zv,z^2,yz,y^2v,y^3)\) なので \(\mu(J)=6<F_1=9\)。\(m>6\) では全 \(\theta_0,\theta_1,\theta_2,\theta_3,\theta_6>0\) であり
\[
J=J'+(xz^2),\qquad
J'=(y^3,yz,z^3,v^{\theta_0},yv^{\theta_1},
y^2v^{\theta_2},zv^{\theta_3},z^2v^{\theta_6}).
\]
常在する最小生成元は \(y^3,yz,z^3,v^{\theta_0}\) の四つ。残りの四候補が新しい最小生成元になる条件は、順に \(\theta_1<\theta_0,\theta_2<\theta_1,\theta_3<\theta_0,\theta_6<\theta_3\)。\(\mu(J)=\mu(J')+1\) なので全 \(m>6\) は次の四剰余で尽くされる。

| \(m\bmod4\) | \(\mu(J')\) | \(\mu(J)\) | actual \(F_1(m,4)\) |
|---:|---:|---:|---:|
|0|5|6|7|
|1|7|8|10|
|2|7|8|9|
|3|5|6|8|

\(w=5,t=4\) では \(J_0=(y^4,yz,x^2z^2,xz^3,z^4)\) の5個。\(y^r\) 列 \(r=0,1,2,3\) の \(\theta_r=\lceil(m-r)/5\rceil\) は非増加で段差が高々一回なので、追加される最小 \(y^rv^{\theta_r}\) は高々2個。\(z,z^2,z^3\) の三列から高々3個。従って \(\mu(J)\le5+2+3=10<11\le F_1(m,5)\)。ここまで有限rank計算は使わない。

#### B5 幅6以上の族は端点上界だけで閉じる

coreを両端点で割ると
\[
Q_C=k[y,z]/(yz,y^{w-1},z^{w-1}),\qquad
P_C=2w-3,\quad\sigma_C=2.
\]
実際、B2の初期idealに端点を加えるとこの単項式商になり、同じ次数・offsetの異なる純内部語は存在しないため、これは元のcore商自体の表示である。
mod \(w\) の内部ステップは \(+1,-1\)。剰余 \(r\) の最短長は \(\min(r,w-r)\) であり
\[
W=1+\sum_{r=1}^{w-1}\min(r,w-r)=1+\lfloor w^2/4\rfloor.
\]
12.2のactual kernel補償付き上界と \(R\le W-w\) より
\[
\beta_1(G)\le P_C+\sigma_C+1+R\le W+w.
\]
これと最小targetとの差は
\[
\binom w2+1-(W+w)=\frac{w(w-3)}2-\lfloor w^2/4\rfloor.
\]
\(w=2h\ge6\) なら \(h(h-3)\ge0\)、\(w=2h+1\ge7\) なら \((h-1)^2-2\ge0\)。従って全 \(w\ge6\) で第一行比較が成立し、特に残っていた \(w=6,\ldots,10\) を覆う。

### 12.7 N4の合成

\(d\ge2\) は12.3で全行が成立。\(d=1\) は12.4で \(i\ge2\)、12.5で一般第一行と全有限offset補題、12.6でその全例外の第一行が成立する。\(w=3\) の同一target、全 \(m\ge w+2\)、全剰余、合成数幅、\(\gcd(m,u)>1\) も含む。第0行1と \(i>4\) のsource消滅を合わせ、N4は任意体・全行で証明された。□

## 13 全場合の最終組立て

物理幅 \(w=g_e-m\) によって分ける。

1. **\(w\le m-2\)。** \(e\ge5\) なら正規化幅 \(u=w/d\le w<m\) なので付録A。\(e=4\) は第12節で証明したN4、\(e=3\) はLan–Tu–Vuの公刊定理、\(e\le2\) は下記の直接計算を使う。
2. **\(w\ge m-1\)。** completionの最小生成系は \(m,m+1,\ldots,2m-1\)。\(e\ge3\) で第4節のcutを一つ選ぶ。\(r=2,3\) は第9節。\(r\ge4\) なら \(\delta\ge a\ge\binom{r+1}{2}\ge10\)。\(e\ge10\) は第10–11節で同じcutの全rankを払う。残る \(5\le e\le9,\delta\ge10\) は付録B。

\(e=1\) は \(\Gamma=\mathbb N\)。\(e=2\) は \(\Gamma=\langle m,n\rangle,\ m<n,\gcd(m,n)=1\) であり、定義式 \(y^m-x^n\) の最低次数項から \(G=k[x,y]/(y^m)\)、Betti列は \((1,1)\)。completionは埋込次元2以上の1次元環なので第一Betti数が1以上、それ以後のsource行は0。

境界 \(w=m-1\) は第2の場合に含まれる。正規化幅と物理幅を区別し、比較先は全段階でactual completionとした。有限体で使う一般形式は第4節の同標数の純超越拡大とBetti数の体拡大不変性で戻す。

以上により、明記した公刊定理と有限整数補題を用いて、P14は全真正数値半群・任意体・全total Betti行で成立する。内部の旧境界定理を未証明仮定として残さない。□

## 14 Leanへ渡す証明単位

中心鎖は数値座標、jump strata、実際の塔、一つの \(H_t\) 列、直接Koszul評価、単一scalar、ordinary target比較である。N4は第12節の内部定理へ置き換わった。有限計算は、証明済み範囲の有限和・最短offset DP・単項式可除判定・厳密有理数の比較として表現できる。

最初にH23・7個の小有理数比較・多項式恒等式と有限整数補題を形式化できる。次に直接Koszulの単位小行列、Tor完全列、数値座標、全称停止・tailをつなぐ。公刊Green、BHP/EK、Kneser、算術列公式、Lan–Tu–Vu、Savchev–Chenは正確なstatementをライブラリへ接続する必要がある。

本稿と検算JSONを未証明の <code>axiom</code> として置いた段階をLean完全証明とは呼ばない。本成果は人間向けの数学的証明稿と再実行可能な有限補題であり、Leanファイル・toolchainはまだ追加していない。

## 付録A 幅側の全生成元数

#### A 定理とtarget

\(\Gamma=\langle m,m+da_1,\ldots,m+da_q,m+du\rangle\)、\(e=q+2\ge5\)、\(0<a_1<\cdots<a_q<u<m\)、\(\gcd(m,d)=\gcd(u,a_1,\ldots,a_q)=1\) とする。任意体・全行で、実際のcompletion \(\langle m,m+1,\ldots,m+du\rangle\) へのP14が成立する。

実効target幅は \(V_{\rm tar}=\min(du,m-1)\ge u\)。算術列のBetti公式から、正の第 \(i\) 行は
\[
 F_i^{\min}(u)=i\binom u{i+1}+\min\{\binom u{i-1},\binom ui\}
 \tag{W1}
\]
以上である。範囲外の二項係数は0。算術列半群環の公式と、その場合の接錐とのBetti一致だけをここで使用する。

#### A 1 実sourceへの移行

整数コアを \(C=k[s^u,s^{u-a_1}t^{a_1},\ldots,t^u]\)、端点を \(x=s^u,v=t^u\)、\(Q=C/(x,v)\) とし、\(P=\dim Q\) とする。次数・offset \((n,b)\) を指数 \(nm+db\) の初期形へ送ると \(C\twoheadrightarrow G_\Gamma\) となる。

\(Q_G=G/(x,v)G\)、\(p=\dim Q_G\)、\(R=\dim(0:_G(x,v))\) とする。核 \(K=\ker(Q\to Q_G)\) の長さ \(P-p\) を残したTor完全列から
\(b_i(Q_G)\le b_i(Q)+(P-p)\binom q{i-1}\)。端点Koszulのhomologyの長さは \((p,p+R,R)\) である。中央の長さはEuler特性から従う。従って二重複体から
\[
 \beta_i(G)\le b_i(Q)+P\binom q{i-1}+R\binom{q+1}{i-1}. \tag{W2}
\]
商のBetti単調性は仮定しない。

offsetの巡回群での最短語長を \(\ell_r\)、\(\ell_0=0\)、\(W=1+\sum_r\ell_r\) とする。各剰余のコアを二端点変数の平面単項式イデアルとして表す。最短点 \((L_r,K_r)\) は \(L_r+K_r=\ell_r-1\) を満たす。極小点はantichainなのでその個数は \(\ell_r\) 以下であり、\(P\le W\)。

実sourceで消えるのは長い表示との競合 \((n,b)\mapsto(n+jd,b-jm)\)、\(j\ge1\) による。\(r+jm=s+cu\)、\(\epsilon_r=[r>0]\) とすれば、競合イデアルの生成点は
\[
 (\max(0,L-jd-c+\epsilon_r-\epsilon_s),K+c).
\]
実socleはこのイデアルの有限cornerに入る。極小点が \(z_s+1\) 個、最小第二座標が \(\kappa_s\) のとき、任意の点 \((p',q')\) に対し \(z_s\le p'+q'-\kappa_s\)。\(j=1\) の最短点を各剰余で使うと、carry総和と \(\sum_s\lceil(m-s)/u\rceil\) はともに \(m\) で相殺される。従って
\[
 R\le W-u.
\]
また \(c-\epsilon_r+\epsilon_s\ge\lfloor jm/u\rfloor\ge1\)、\(jd\ge1\) なので第一座標は \(\max(H_x-2,0)\) 以下。各剰余のcorner数もこの値以下であり、
\[
 P\le W,\qquad R\le\min\{W-u,u\max(H_x-2,0)\}. \tag{W3}
\]
この平面corner導出の一般変数数での座標記述は付録C §§2–4にある。純v冪の存在と最小第二座標の並べ順は第12.2節F4–F6と同じ証明を用いる。変数数に依存しない原証明だけを使用し、その後の有限core campaignは使用しない。

#### A 2 密な幅

\(t=u-1-q\le q\) とする。非零のコアwordの長さ2以降のprefix剰余はすべて欠落offsetで、相異なる。従って非零次数は \(n\le t+1\)、\(H_x\le t\)。\(q+1>u/2\) なので全剰余は長さ2以下で到達し、
\[
 W=q+1+2t,\quad P\le q+1+2t,\quad R\le t,
 \qquad t\le2\Rightarrow R=0. \tag{W4}
\]

同じHilbert関数のlex標準単項式のうち最初の \(j\) 変数にある個数を \(S_j(n)\) とすると、極小生成元の数は
\(g_j(n)=S_j(n-1)-S_j(n)+S_{j-1}(n)\)。次数についてtelescopingし、BHP/EKを適用すると
\[
 b_i(Q)\le i\binom{q+1}{i+1}+K\binom{q-1}{i-1},\quad
 K=\sum_{n\ge2}\sum_{j=1}^q S_{j-1}(n).
\]
\(\binom{r+1}{2}\ge2t\)、\(r\le q\) なら、全lex標準単項式は末尾 \(r\) 変数に支持される。親子incidenceの指数重みを数えると
\[
 K\le\sum_{n\ge2}\frac{r-1}{n+1}h_n\le\frac{2t(r-1)}3. \tag{W5}
\]
全行で同じlex idealを使用する。

\(q\ge4\) では、(W2)–(W5) とtargetのVandermonde展開から、\(t=2,3\) の差はそれぞれ
\[
 (q-3)\binom q{i-1}+i\binom{q+1}{i-1}-2\binom{q-1}{i-1},
\]
\[
 (2q-4)\binom q{i-1}+(3i-3)\binom{q+1}{i-1}-4\binom{q-1}{i-1}
\]
以上で、非負。\(4\le t\le q\) では \(r=t\) を選び、差は少なくとも
\[
 \left[\frac{5t^2-17t-6}{6}+(t-1)(q-t)\right]\binom q{i-1}\ge0.
\]
\(t=4+z\) とすれば括弧の6倍は \(5z^2+23z+6+6z(q-t)+18(q-t)>0\)。

\(t=0\) は算術列公式による最小幅。\(t=1\) はコアが \((1,q,2)\)、端欠落なら \((1,q,1)\) で次数3以降0となる。内部欠落では二つの置換フォームから元のKoszul行列に対角 \(\pm1\) 小行列を取り、
\[
 b_i(Q)=i\binom{q+1}{i+1}-2\binom q{i-1}
 +\binom{s+1}{i-r'}+\binom{r'+1}{i-s},\quad r'+s=q.
\]
最後の二項は、互いに素な二ブロックに固定点を加える二つの包含単射によって \(\binom{q+2}i\) と \(\binom{q+2}{i-1}\) の双方以下となり、(W1)で払える。端欠落も一つの置換フォームの同じ単位小行列で閉じる。全パラメータの単射と行の端点は、付録D §§3–5 の原証明通りであり、有限の行列証明書を仮定しない。

#### A 3 疎な幅の短いtail

\(e\ge8\)、\(u\ge2e-2\) とする。\(a=e-1\)、\(s=\lfloor e/2\rfloor\) と置く。Kneserから
\[
 W\le B(u)=u+\sum_{j\ge0}(u-a-sj)_+.
\]
\(\Delta=u-a=sk+b\)、\(0\le b<s\) と書けば
\[
 B(u)=u+\frac{\Delta^2}{2s}+\frac\Delta2+\frac{b(s-b)}{2s}
 \le B_{\rm cap}=u+\frac{\Delta^2}{2s}+\frac\Delta2+\frac s8,
 \qquad B(u)\le\frac{u^2}{e-1}. \tag{W6}
\]
後者は、\(u=a+sk+b\) を代入した差の \(2a\) 倍が
\(s(2s-a)k^2+ask+2(2s-a)kb+2b^2\ge0\) であることによる。

Artin親子計数と次数0→1のKoszul単位小行列から (W2) は
\[
 \beta_1\le\frac{e+3}{3}B-u+\frac{e(e-1)}6=:U_1,
\]
\[
 \beta_i\le B\binom ei-u\binom{e-1}{i-1}-\binom{e-1}{i+1}=:U_i
 \quad(2\le i\le e).
\]
\(D_{\rm cap}=\binom u2+1-[(e+3)B_{\rm cap}/3-u+e(e-1)/6]\) とする。
\(e=2s+1-h\)、\(h=0,1\)、\(s=v'+4\)、\(u=2e-2+z\) と書けば
\[
\begin{aligned}
24sD_{\rm cap}\big|_{h=0}={}&62v'^3+40v'^2z+556v'^2+4v'z^2\
&+220v'z+1496v'+240z+1056,\\
24sD_{\rm cap}\big|_{h=1}={}&62v'^3+40v'^2z+509v'^2+4v'z^2\
&+216v'z+1244v'+4z^2+248z+788.
\end{aligned}
\]
全係数が非負で、定数が正なので第一行が閉じる。

第二行は
\[
 2\binom u3-U_2\ge\frac u6[2u^2-(3e+6)u+6e-2]+\binom{e-1}3.
\]
\(e=8+v'\)、\(u=2e-2+z\) なら中括弧は
\(2v'^2+5v'z+16v'+2z^2+26z+18>0\)。高次行へは
\[
 T_i(u)=\frac{i\binom u{i+1}}{\binom ei}+\frac{ui}{e}
       +\frac{(e-i)(e-i-1)}{e(i+1)}
\]
を用いる。\(T_i(e)=e-1+i/e\)、増分は
\(i\binom ui/\binom ei+i/e\) であり、\(i\) とともに増加する。従って \(T_i\ge T_2\ge B\) から全行が閉じる。平方根閾値や剰余anchor帰納は不要である。

#### A 4 6・7生成元も同じ仕組みで閉じる

\(e=6,q=4\) の密な部分は第2節で \(u\le9\) まで閉じる。\(u=10+z\) では (W6) の第一行差は \(z-1/8\) なので \(z\ge1\) は正。\(z=0\) は厳密値 \(B(10)=17\) により \(U_1=46=\binom{10}2+1\)。高次行は
\[
 2\binom u3-U_2\ge (u-10)(u-3)(u+1)/3\ge0
\]
と \(T_i\ge T_2\) で閉じる。

\(e=7,q=5\) の密な部分は \(u\le11\) まで閉じる。Artin incidenceを一段強めると
\[
 b_1(Q)-P\le4+h_1+h_2/3\le4+5+15/3=14.
\]
従って \(\beta_1\le3B-u+14\)。\(u\ge12\) では \(B\le u^2/6-u/2+27/8\) より第一行差は \(2u-185/8>0\)。第二行の中括弧は \(u=12+z\) で \(2z^2+21z+4>0\) となり、同じ高次行移行が使える。

#### A 5 5生成元の最後の小幅を列挙せず処理する

\(q=3\) とする。\(u=4\) は最小幅、\(u=5\) はone-gapである。

\(u=6,t=2\) では (W4)–(W5) より \(P\le8,R=0,K\le2\)。ordinary部分との余裕は \(i\binom4{i-1}-2\binom2{i-1}\)。\(i\ge2\) は非負、\(i=1\) の不足1は (W1) の最小補正項1で払う。

\(u=7,t=3\) では \(P\le10,R\le3,K\le4\)。\(H_x\le2\) なら \(R=0\) で、余裕は
\(2\binom3{i-1}+3i\binom4{i-1}-4\binom2{i-1}\ge0\)。
\(H_x\ge3\) なら \(Q_4\ne0\)、prefix上界から \(Q_{\ge5}=0\)。従って \(h_2,h_3,h_4\ge1\)、総和が6以下なので各々4以下。3変数の辞書順最小4単項式を数えると \(S_1(2..4)=0\)、\(S_2(2),S_2(3)\le1\)、\(S_2(4)=0\)、ゆえに \(K\le2\)。余裕は
\(2\binom3{i-1}+(3i-3)\binom4{i-1}-2\binom2{i-1}\ge0\)。

\(u\ge8\) は4元巡回集合 \(A=\{0,a,b,c\}\) にKneserを適用する。非antipodalなら \(|nA|\ge\min(u,3n+1)\)。stabilizerの大きさと含むcoset数がともに2のときだけ、例外 \(u=2h,A=\{0,t,h,t+h\}\)、\(\gcd(t,h)=1\) となる。

非例外では
\[
 B_3(3j)=(3j^2+j+2)/2,\quad B_3(3j+1)=(3j^2+3j+2)/2,
 \quad B_3(3j+2)=(3j^2+5j+4)/2.
\]
\(b_1(Q)\le\lfloor P/2+5\rfloor\) から
\(\beta_1\le\lfloor(5/2)B_3-u+5\rfloor\)。\(u\ge9\) の差はそれぞれ
\((3j^2+j-26)/4,(3j^2+3j-22)/4,(3j^2+5j-24)/4>0\)。\(u=8\) は \(B_3=13\) により \(\beta_1\le29=\binom82+1\)。

例外は直接 \(Q=k[y,z,w]/(yz,z^2,zw,(y,w)^h)\) と書ける。\(P=\binom{h+1}2+1\)、\(b_1=h+4\)、\(W=h^2-h+2\) なので第一行差は \((h^2+h-12)/2\ge0\)。

全 \(u\ge8\) の高次行は、3変数Artin商の \(b_1\le P+2,b_3\le P-1,b_2\le2P\) と端点Koszulから
\[
 \beta_2\le5P+4R,\quad\beta_3\le4P+6R-1,\quad
 \beta_4\le P+4R,\quad\beta_5\le R.
\]
\(P\le W\le u^2/4\)、\(R\le u^2/4-u\) を代入する。第二行差は \(u(4u-7)(u-8)/12\ge0\)。残りは \(u=8\) の容量 \((210,224,140)\) が上界 \((160,80,16)\) より大きく、\(\binom uk/u^2\) は \(k\ge3\) で増加するから閉じる。

以上は全パラメータの紙上評価であり、68個の5生成元core、785個の6生成元core、210個の7生成元coreを含め、有限core campaignを呼ばない。任意体性は元の \(\pm1\) 小行列と任意標数のBHP/EKに基づく。比較先は全段階で実際のcompletionのままである。□

## 付録B 小ordinary領域

任意体、actual atoms、実際のordinary targetを固定する。証明範囲は \(5\le e\le9\)、\(m\ge e+10\)。旧小生成元数主定理、MED、D1、D2を仮定しない。公刊BHP/EK以外の必要な有限化と支払いを以下で証明する。

#### B 1 全profileに一つの明示最大列

e≥2、m≥e+1、2≤ρ≤m−1 とし、N_d=C(e+d−1,d)。ρはfirst-hit。m>N_ρなら次元上不可能なので除く。残るprofileについて

    Hcap_0=1, Hcap_1=e,
    Hcap_d=min(m−1,N_d)  (2≤d<ρ),
    Hcap_d=m            (d≥ρ)

と定める。特にe6,m23ではHcap_2=21であり、誤ったh2=22を使わない。任意の同profile実Hilbert列Hは、全pre-hit次数でh_d≤Hcap_dを満たす。

lex順X1>⋯>Xe、標準単項式は辞書順最小h_d個とする。S_j(d,h)はそのうちX1,…,Xjだけを含むものの数。最大変数j、次数dの極小生成元数はstable shadowの対応により

    g_j(d)=S_j(d−1,h_{d−1})−S_j(d,h_d)+S_{j−1}(d,h_d)。

w_j=C(j−1,i−1)と置いて、terminal次数ρ+1まで全てを数えると

    L_i(H,ρ)
      = i C(e+1,i+1) −Σ_j S_j(ρ+1,m)w_j
        +Σ_{d=2}^{ρ+1}Σ_j S_{j−1}(d,h_d)w_j。       (T)

これは厳密なtelescope。負号のterminal項とd=ρ,ρ+1の項は固定。各S_jはhについて非減少で、残る係数は非負。したがって全iで同時に

    β_i(G)≤L_i(H,ρ)≤L_i(Hcap,ρ)。                   (E)

第一不等式は同Hilbert関数の次数別BHP/EKとactual cutoffから従う。lex自身のregularityや任意商Betti単調性を仮定していない。

(E)を上界として使うだけならHcapの実現可能性は不要。さらに、Hcapは実際にMacaulay admissibleなHilbert列でもある。

- 前次数がN_dなら次の最大値はN_(d+1)なので、capへの移行もhitへの移行も許される。
- 一定m−1および一定mの遷移はn^{<d>}≥nから許される。
- 最後のm−1→mの直前次数はd=ρ−1≤m−2。このときn=m−1≥d+1なのでn^{<d>}≥n+1=m。

最後の一般事実はMacaulay展開 n=Σ_{j=s}^d C(a_j,j) から直ちに従う。増長との差はΣ C(a_j,j+1)≥0。差が0なら全a_j=jで、nは高々d個の1の和だからn≤dとなり矛盾。したがって差は少なくとも1。

以上により、Hcapは固定profileのformal Hilbert宇宙の全行最大を同時に達成する。数値半群としての実現可能性は主張しない。巨大DPで行別argmaxや全pathを探す必要はなくなる。

#### B 2 actual source の有限化を定義から証明する

ここから最終filtered ordinary枝を独立に閉じる。Γ=〈m,m+b1,…,m+b_(e−1)〉を真正な数値半群、b_j>0、R=k[[Γ]]、G=gr_𝔪 R、x=(t^m)* とする。offsetは正規化前の実整数を使う。

##### 2.1 exact offset 列

offset加法モノイドの元Aを正のb_jで表す最短語長をf(A)とする。f(0)=0、負または到達不能Aではf(A)=∞。数値指数s=nm+Aが長さnの表示を持つ必要十分条件はf(A)≤n。これより長いn+j文字の表示を持つ必要十分条件はf(A−jm)≤n+jである。従って次数nの非零初期単項式がexact offset Aにある条件は

    f(A)≤n<g(A),  g(A)=min_{j≥1}(f(A−jm)−j)。       (C1)

x乗法はこのAを固定してnを1増やす。従って各非空列は一つのk[x]自由列、またはk[x]/(x^ℓ)列になる。同じ次数の異なるAは異なる数値指数なので線形独立であり、全単項式初期形がこれらの列で尽くされる。

各剰余r mod mについて到達可能offsetの最小値α_rを選び、f_r=f(α_r)と置く。全剰余が存在するのはgcd(m,b1,…)=1による。α_0=f_0=0。最小offset最短語の任意prefixもその剰余の最小offset最短語である。小さいoffset、または同じoffsetの短い語に置換できれば、全語の最適性に反する。prefix剰余が反復すれば、その間の正の零和offsetを除いてα_rを小さくできるので

    f_r≤m−1。                                    (C2)

α_rの列は永久に生きる。それ以外の同剰余offsetはA=α_r+jm (j≥1)で、(C1)から

    g(A)≤f_r−j≤m−2。

従って全有限列は次数m−3までに終わり、全m本の自由列は次数m−1までに開始する。よって

    h_n=dim_k G_n=m  (n≥m−1)。                    (C3)

任意nでh_n≤mでもある。同じ剰余の二つの異なる数値指数s<s+jmがともにorder nなら、後者は前者のn文字表示にj個のmを加えた長い表示を持ち矛盾する。h_n≥1はt^(nm)のorderが正確にnであることによる。

##### 2.2 first-hit の安定と実Tor cutoff

任意のI=𝔪^nは、各剰余の最小数値指数w_(n,r)を使い

    I=⊕_{r mod m} k[[t^m]] t^(w_(n,r))

と書ける。従ってDVR k[[t^m]]上自由rank mであり、length(I/t^m I)=m。t^m I⊂𝔪I⊂Iより

    0→𝔪I/t^m I→I/t^m I→I/𝔪I→0。

h_n=mなら最初の長さが0なので𝔪^(n+1)=t^m𝔪^n。この等式を𝔪倍して以後に伝播できる。従ってρ=min{n:h_n=m}は(C3)によりρ≤m−1、以後h_n=mで、x:G_n→G_(n+1)はn≥ρで全射、同じ次元mなので同型。

G/xGは内部次数ρ以下、(0:x)は次数ρ−1以下に集中する。一変数Koszul H1=(0:x)(−1)も内部次数ρ以下。他のe−1変数のp番目Koszul鎖群で加わる内部次数はpだから、二重複体のスペクトル系列の合計ホモロジー次数i=p+q (q=0,1)では内部次数ρ+p≤ρ+iである。従って

    β_(i,j)(G)=0  (j>ρ+i)。                       (C4)

この証明は任意体で成立し、CM性、一般線形形式、lex自身のregularityを仮定しない。§1の(T),(E)に必要な数学的有限化は(C1)–(C4)で独立に得られた。

##### 2.3 x列の総数 P_x の二次上界

非空有限列A=α_r+jmではf(A)≥1、f(A)<g(A)≤f_r−jなのでj≤f_r−2。各rに高々max(f_r−2,0)本の有限列がある。f_rを昇順に並べるとf_(j)≤j (0≤j≤m−1)。実際、最長の最小offset最短語のprefixが長さ0,…,Lの相異なる剰余を与え、j≤Lでは長さ≤jの剰余がj+1個あり、j>Lでは全長さがL以下。

従って、P_x=dim G/xG、N_x=dim(0:x)について

    P_x≤m+Σ_r max(f_r−2,0)
       ≤m+Σ_{j=0}^{m−1}max(j−2,0)
       =(m²−3m+6)/2=:P(m),
    N_x=P_x−m。                                  (C5)

最後の等式は自由列がm本、有限列はheadとx-annihilatorを各1個持つことによる。これでtailに必要なP_x評価も独立に証明した。

#### B 3 5本の ordinary tail を有理anchorと差分で証明する

##### 3.1 第一行のharmonic上界

同Hilbert関数のlex標準単項式B_d（個数h_d）を使う。すべての直接約数がB_dにある次数d+1の子の集合をC_dとする。各子uから親u/X_jへの重みをu_j/(d+1)とすれば、各子の総重みは1、各親から全候補子への総重みは高々(d+e)/(d+1)。従って

    |C_d|≤(d+e)h_d/(d+1)。

新しいlex極小生成元はC_d\B_(d+1)なので、その数は右辺−h_(d+1)以下。(C4)と次数別BHPにより、実β1ではd=1,…,m−1だけを数えればよい。h1=e、h_m=m、h_d≤mを使ってtelescopeすると

    β1(G)≤e−m+(e−1)Σ_{d=1}^{m−1}h_d/(d+1)
          ≤(e−1)mH_m−(3e−1)m/2+e(e+1)/2=:A_e(m)。 (A1)

H_m=Σ_{j=1}^m1/j。これらの有理重みは整数個数の評価に使い、基礎体内の除法ではない。

D_e(m)=C(m,2)−A_e(m)とすると恒等的に

    ΔD_e(m)=m+(e+1)/2−(e−1)H_m,
    Δ²D_e(m)=1−(e−1)/(m+1)。                       (A2)

次の有理anchorは全て正。現checkerはFractionで有限和から新たに再計算する。

|e|T_e|D_e(T_e)|ΔD_e(T_e)|
|---:|---:|---|---|
|5|16|28529/45045|986861/180180|
|6|24|87527047/14872858|3076971505/356948592|
|7|32|13190245423022/1504203675975|280360191738961/24067258815600|
|8|42|17040044863244869/474156254847600|46124404177135267/2844937529085600|
|9|54|42360392440805889237573/380206848900550521850|153275837511203454076291/6843723280209909393300|

m≥T_eでは(A2)の第二差分が正。従ってΔDとDが以後ずっと正となり、全m≥T_eの第一行がordinary容量以下。

##### 3.2 第二行から全高次行

x-Koszul homologyの次元はP_x、P_x−m。他のe−1変数との二重複体の鎖群次元と(C5)から

    β_i(G)≤P_x C(e−1,i)+(P_x−m)C(e−1,i−1)
          ≤P(m)C(e,i)−mC(e−1,i−1)=:U_e(m,i)。      (A3)

第二行の差G_e(m)=2C(m,3)−U_e(m,2)は明示的三次式

    12G_e(m)=4m³−[12+3e(e−1)]m²
              +[8+3(e−1)(3e+4)]m−18e(e−1)。

その前進差分は

    ΔG_e(m)=m²−[1+e(e−1)/2]m+(e−1)(e+2)/2,
    Δ²G_e(m)=2m−e(e−1)/2,  Δ³G_e(m)=2。            (A4)

|e|T_e|G_e(T_e)|ΔG_e(T_e)|Δ²G_e(T_e)|
|---:|---:|---:|---:|---:|
|5|16|114|94|22|
|6|24|343|212|33|
|7|32|305|347|43|
|8|42|238|581|56|
|9|54|360|962|72|

全anchorが正、第三差分が2なので、全m≥T_eでG_e(m)>0となる。

F_i=iC(m,i+1)と置く。m≥e+1、2≤i<eでは

    [F_(i+1)/C(e,i+1)] / [F_i/C(e,i)]
       =(i+1)²(m−i−1)/(i(i+2)(e−i))>1。

m−i−1≥e−iと(i+1)²>i(i+2)による。一方U_e(m,i)/C(e,i)=P(m)−mi/eはiとともに減少する。従って第二行の比較だけで全i=3,…,eが従う。i>eではsourceが0、i0は双方1。以上で5本tailの全体・全行を、過去のtail定理を仮定せずに証明した。

#### B 4 最後のfirst-hitが全行を同時に最大化することの再証明

§1のcapped列のtruncated lex上界をL_i(ρ)、最大変数jの全極小生成元数をT_j(ρ)とする。ここでは必要なe≥5、m≥15だけを扱う。source_materialのR42-LX-MAXの機構を整数恒等式から再確認する。

次数mの最初m個のlex標準単項式は全てX_eを含む。次数m−1ではX_eを含まないものはX_(e−1)^(m−1)だけ。従って(T)から

    T_j(m−1)=j+Σ_{d=2}^{m−2} S_(j−1)(d,b_d)       (j<e),
    T_e(m−1)=e−m+1+Σ_{d=2}^{m−2}S_(e−1)(d,b_d),
    b_d=min(m−1,N_d)。                            (M1)

ρ≤m−2について、次数ρのm番目のlex最小単項式をuとし、v=maxvar(u)、k=e−vと置く。ρ以後はN_d≥mなのでcap b_d=m−1。共通の早い項を消すと、j<eについて厳密に

    T_j(m−1)−T_j(ρ)
      =[S_j(ρ+1,m)−S_(j−1)(ρ+1,m)]−1_(j>v)
       +Σ_{d=ρ+1}^{m−2}S_(j−1)(d,m−1)
      ≥−1_(j>v)。                                (M2)

したがって負になる可能性があるのはj=v+1,…,e−1の高々k−1個だけで、各損失は高々1。

ρ≤m−3ではa=1_(k≥1)、b=1_(maxvar(u_(ρ+1,m))≤e−1)と置くと

    T_e(m−1)−T_e(ρ)
      =1−a−b+Σ_{d=ρ+2}^{m−2}S_(e−1)(d,m−1)。     (M3)

各和項は1以上。純粋冪X_(e−1)^dのlex rankはd+1≤m−1だからである。

- k0ではa0、b≤1なので(M3)は非負。
- k1でρ≤m−4なら少なくとも一項が1−a−bの不足を払う。ρ=m−3なら、次数m−2のm番目単項式はX_(e−2)X_e^(m−3)なのでb0、和は空でも差0。
- k≥2ではX_v^ρが末尾k+1変数だけの単項式の最後に位置するので、C(ρ+k,ρ)≤m。ρ,k≥2、ρ+k≥5ならC(ρ+k,ρ)≥ρ+k+3。内側二項係数の最小値C(n,2)とn(n−1)/2≥n+3 (n≥5)から従う。従ってm−ρ≥k+3。(ρ,k)=(2,2)でもm≥15なら同じ不等式が成立する。(M3)の項数はm−ρ−3なので、差は−1+(m−ρ−3)≥k−1。

ρ=m−2では別に、m番目の単項式はX_(e−2)X_e^(m−3)だからk0。直接(M1),(T)を引くとe番目の差0、他は(M2)で非負。ρ=m−1は等号。

よって常に最後のslot eの増分はmax(0,k−1)以上。EK重みw_j=C(j−1,i−1)は非負かつjについて非減少なので、slot eの増分が全負slotを払う。全iで同時に

    L_i(ρ)≤L_i(m−1)。                             (M4)

これは隣接ρの単調性を主張していない。全てのρに対する共通最大点を直接示した。例外的小mの処理も今回のm≥15では不要。

#### B 5 83組の整数比較でordinary残余を閉じる

§2の有限化、§1の正係数telescope、§4の最大first-hit補題から、有限部分で必要なのはρ=m−1の次の83組だけ。

    e5: m15（1組）、e6: m16..23（8組）、e7: m17..31（15組）、
    e8: m18..41（24組）、e9: m19..53（35組）。

保存checkerの主要再実行は

    python -B checks/verify_small_ordinary.py

出力 `certificates/small_ordinary.json`。**83profile・665 scalar行比較で全不足0**。最小余裕は105−38=67。profile意味内容SHA-256は `e10afc786ae3d55a1d35e65533696792ebf4ff4daea18c61806594623d09c65a`。同じ実行が§3の5本tail anchorと差分恒等式も有理数で新たに計算する。

従って任意の体、真正なe生成元数値半群について

    5≤e≤9, m≥e+10 ⇒ β_i(G)≤iC(m,i+1) (i≥1)。       (Bord)

ordinary completionのBetti数は右辺なので、この残余BordinaryのP14が成立する。第0行は双方1。数学的入力はここで再証明したactual列、first-hit、cutoff、incidence、Koszul鎖群評価、telescope、最大点の整数組合せ補題、および任意標数BHP/EKである。MED/D1/D2と過去の小生成元数主定理をこの(Bord)の仮定に置かない。

全2315profileの検算は(M4)を別経路で診断するために保存するが、最終証明の有限比較は83組で足りる。整数checkerによる計算支援証明であり、Lean形式化の完了とは区別する。

## 付録C 一般変数数のactual endpoint移行

#### C 1. 対象と完備化容量

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

各項は v について非減少である。従って実 source の上界を \(F_i^{\min}(u)\) 以下と示せば十分である。範囲外の二項係数は 0 とする。算術列公式は第12.1節で明記した公刊定理を使用する。

なおこの m>u 領域では最小生成性は自動的でもある。もし生成元 \(m+da\) が長さ \(l\ge2\)、offset 和 B の語なら、\((l-1)m=d(a-B)\)。互いに素性から \(l-1=jd,a-B=jm\) で j>=1 となり、a<=u<m に矛盾する。

#### C 2. 整数コアと有限 Artin 基底

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

#### C 3. 実 kernel による補償

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

#### C 4. m,d に一様な実 socle 上界

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

大きなjで第一閾値は0となるため各T_sは純v冪を含む。T_s の極小点が z_s+1 個、第一座標昇順で最後の第二座標、すなわち最小第二座標が kappa_s なら、任意の (p,q) in T_s について z_s<=p+q-kappa_s。この点を割る極小点の左右の個数を、それぞれ座標減少幅で数えればよい。各最短点に (4.2) の j=1 を適用する。r->(r+m) mod u は置換であり、carry の総和は m。一方 kappa_s>=ceil((m-s)/u) で、その和も m。第一座標は L_r 以下だから

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

#### C 5. Artin 上界と全体の screen

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

#### C 6. 反射と最小幅

A を {u-a:a in A} に反射すると、コアの基底は (n,b)->(n,nu-b) で移り、内部変数の置換で Q の Koszul homology も一致する。ただし実 source の H_x、R_hat は向きに依存する。証明書では Q の計算だけを共有し、P_C,W,H_x,R_hat と支払い式は全ての元の向きで計算し直す。

最小幅 u=q+1=e-1 は完全な算術列 source である。算術列公式を全 c で最大化すると、その全行は i*C(e,i+1) 以下。V>=e なら完備化の最小容量がこれを支払う。V=e-1 の場合は d=1 または m=e。前者は source と完備化が同じで、後者は両者とも最大埋込次元 m の接錐で Betti 数が i*C(m,i+1) に一致する。したがって最小幅は全 m,d、全体で閉じる。

## 付録D 一欠落幅の全称証明

#### D 1. 結論と入力境界

**定理 WOG.** $e=q+2\ge5$、$u=e$、$m>u$ とし、任意の体 $k$ 上で

\[
\Gamma=\langle m,\ m+da\ (1\le a\le u-1,\ a\ne h),\ m+du\rangle,
\qquad 1\le h\le u-1,\quad d\ge1,\quad\gcd(m,d)=1
\]

とする。この真正な $e$ 生成元数値半群の接錐は、その区間完備化の接錐に対し、
すべての Betti 行で P14 を満たす。標数 2 を含むすべての体に同じ証明が適用される。

以下は $q,m,d,h$ に上限を置かない証明である。有限証明書を使わない。

使用する端点移行は付録C §§1–4で証明した次の式である。
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

#### D 2. 一欠落コアの全基底と実 socle

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

#### D 3. 双フォームの原単位 minor

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

#### D 4. 二つの包含写像による全行支払い

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

#### D 5. 端欠落の全行

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
