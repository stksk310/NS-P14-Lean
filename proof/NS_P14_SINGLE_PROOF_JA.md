# NS P14 Lean化に向けた単一証明

2026年11月9日。論文ではなく、定義・補題・有限計算・最終結論を一つにつないだ数学的作業稿である。

**判定。添付資料の低生成元数閉鎖と幅側閉鎖を補題として採用すれば、下記の一つの鎖でP14に到達する。歴代の閉鎖集合の巨大な和集合は不要である。ただし、その二つの旧閉鎖補題の全祖先・有限計算を今回独立に再検証したものではなく、無条件の自己完結した完全証明、またはLean検証済み証明と判定する段階にはない。**

中心となる改善は、既存の塔の厳密な式から

\[
 H_1=\delta-a+\ell\le m-1-a
\]

を残すことである。これにより、大きい生成元数側の境界を元資料の \(e\ge274\) から \(e\ge13\) に下げる。改善部分の200本の無限rayを、有理数で新しく検算した。

## 1 命題と残す境界補題

\(\Gamma\subset\mathbb N\) を数値半群とし、その実際の最小生成系を
\(m=g_1<\cdots<g_e\)、\(\delta=m-e\) とする。体 \(k\) は任意とし、

\[
 R=k[[t^\Gamma]],\quad G=\operatorname{gr}_{\mathfrak m}R,
 \qquad\widetilde\Gamma=\langle m,m+1,\ldots,g_e\rangle.
\]

証明対象は、それぞれの**最小多項式表示**に関するtotal Betti数の比較

\[
 \beta_i(G;k)\le\beta_i(G_{\widetilde\Gamma};k)
 \quad(i\ge0). \tag{P14}
\]

範囲外の二項係数を0とする。\(e=1\) は \(\Gamma=\mathbb N\) なので自明である。

本文で継承する非標準の境界補題は、次の二つに限定する。

| 補題 | 採用する数学的内容 | 資料上の根拠 |
|---|---|---|
| B 小生成元数 | \(e\le12\) なら、実際のcompletionに対して任意体・全行のP14 | 現行再構成版R39と、そのR38以前の小生成元数定理 |
| W 幅側 | \(e\ge8\)、\(d=\gcd(g_2-m,\ldots,g_e-m)\)、\(u=(g_e-m)/d<m\) なら、実際のcompletionに対して任意体・全行のP14 | R40-WALL。端点移行、最小幅、一欠落、幅tailを含む |

ここでB、Wは公刊古典ではなく、添付研究資料中の証明を採用した補題である。出典の版・ハッシュ・残る検証境界は [監査票](AUDIT_JA.md) に記す。これらの真偽をPASSラベルから推論しない。

以下では、B、W以外の中心機構を定義からつなぎ直す。公刊入力として、Greenの超平面制限定理、Peevaのlex連続消去定理、Eliahou–Kervaire公式、Eliasのmicroinvariant上界を使う。

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

## 3 数値的な総量

各非零剰余 \(\rho\bmod m\) について、正のoffset \(g_i-m\) の和でその剰余を与える最小値を \(b_\rho\)、それを実現する最短語長を \(l_\rho\) とし、

\[
 s_\rho=\operatorname{ord}(\omega_\rho),\qquad
 L_\rho=(\omega_\rho-b_\rho)/m
\]

と置く。最小性から \(1\le s_\rho\le L_\rho\le l_\rho\) である。

Eliasのmicroinvariant定理から、\(L_\rho\le\delta+1\) を得る。ここで使用する同定は明示的である。\(W_0=k[[t^m]]\)、first neighborhood ringを

\[
 R'=k[[t^m,t^{g_2-m},\ldots,t^{g_e-m}]]
\]

とすると、

\[
 R=\bigoplus_\rho W_0t^{\omega_\rho},\quad
 R'=\bigoplus_\rho W_0t^{b_\rho},\quad
 R'/R\simeq\bigoplus_\rho W_0/(t^m)^{L_\rho}.
\]

よって \(L_\rho\) は同定理のmicroinvariantsそのものであり、同定理の \(m-e+1\) 上界が適用される。有限体では先に純超越拡大し、数値的な \(L_\rho\) が変化しないことを用いる。

\(v_\rho(q)=\operatorname{ord}(\omega_\rho+qm)\) とすると、

\[
 v_\rho(q+1)\ge v_\rho(q)+1,
 \qquad v_\rho(q)=L_\rho+q\quad(q\ge l_\rho-L_\rho).
\]

後者は、最小offset語に \(m\) を加えればその長さが実現し、それより長い表示はさらに小さいoffsetを与えてしまうことによる。したがって、各剰余で増分の余剰を足すと

\[
 \sum_{\tau\text{ in residue }\rho}(d(\tau)-1)=L_\rho-s_\rho. \tag{3.1}
\]

最短offset語のprefixも、対応する剰余の最短offset・最短長の語であり、prefix剰余は相異なる。語長を昇順に並べれば \(l_{(j)}\le j\) である。そこで

\[
 \sum_{\rho\ne0}(L_\rho-1)
 \le\sum_{j=1}^{m-1}\min(\delta,j-1)
 =\delta\left(e+\frac\delta2-\frac32\right).
 \tag{3.2}
\]

以下では

\[
 V=e+\frac\delta2-\frac32,\qquad M=m-1
\]

と書く。\(V\) は物理幅や正規化幅とは別の数値資源である。

## 4 一つの線形cutを固定する

ここから \(e\ge13\) とする。
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

総和の等式には (3.1) を使う。各剰余でApéryの \(s_\rho-1\) とterminalの \(L_\rho-s_\rho\) が合計 \(L_\rho-1\) となる。

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

## 6 有限加群のharmonic不等式

\(P\) 上有限長の加群 \(Z\) に対し、

\[
 b_i(Z)=\dim_k\operatorname{Tor}_i^P(Z,k),\qquad
 c_j(Z)=\sum_{i=0}^j(-1)^{j-i}b_i(Z),\qquad c_r(Z)=0.
\]

これらは非負のgeneric syzygy ranksである。\(Z\) が次数 \(b\) のみで極小生成されるなら、任意体で

\[
 c_j(Z)\le\binom{r-1}{j}
 \sum_{t\ge0}\frac{j}{t+j}\dim Z_{b+t}
 \qquad(1\le j\le r-1). \tag{H}
\]

証明を記しておく。極小表示 \(P(-b)^q\twoheadrightarrow Z\) の核の斉次initial submoduleを取る。各内部次数でKoszul鎖群の次元は固定され、交代部分和はその鎖群の交代部分和から次の境界rankを引いたものである。特殊化で境界rankは増えないので、\(c_j\) は減少しない。initial quotientは同じshiftを持つArtin単項式環の直和である。

各直和成分を、同一Hilbert関数のlex ideal \(L\) へ替える。Peevaの連続消去定理による隣接二項の消去は、ちょうど一つの \(c_j\) を減らし、他を変えない。したがってlexで上から評価できる。

lexの標準単項式集合を \(D\)、その最初の \(s\) 変数に含まれる部分を \(D^{(s)}\) とする。stable idealのEK公式と交代二項係数の和から

\[
 c_j(P/L)=\sum_{s=j}^{r-1}\binom{s-1}{j-1}|D^{(s)}|. \tag{6.1}
\]

ここで最大変数 \(s+1\) の極小生成元は、\(D^{(s)}\) の各単項式から出る有限な \(x_{s+1}\)-chainの終端と一対一に対応する。stabilityが終端の極小性を保証する。

標準単項式は変数添字を増やす操作で閉じるので、各次数 \(t\) で

\[
 \frac{|D_t^{(s)}|}{\binom{s+t-1}{t}}
 \le\frac{|D_t|}{\binom{r+t-1}{t}}. \tag{6.2}
\]

例えばstars-and-barsで、一様な次数 \(t\) 単項式を一様な \(t\)-部分集合へ対応させる。母集合を \([N]\) から \([N+1]\) へ増やすとき、確率 \(t/(N+1)\) で一様に選んだ要素を \(N+1\) へ替え、それ以外では保持する。この操作は一様分布を保ち、整列した各座標を下げない。このcouplingを反復すれば (6.2) を得る。

最後にhockey-stick恒等式

\[
 \sum_{s=j}^{r-1}\binom{s-1}{j-1}\binom{s+t-1}{t}
 =\frac{j}{t+j}\binom{r-1}{j}\binom{r+t-1}{t}
\]

を使えば (H) が従う。分数は次元の数値評価であり、基礎体の中で除算する操作ではない。

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

## 9 二本と三本のcutは直接閉じる

\(r=2\) なら (7.3) と \(H_1\le2\delta\) により

\[
 c_1(G)-L_1\le\frac52\delta+\frac12S
 \le\delta\left(\frac52+\frac V2\right)
 \le\delta(V+1),
\]

最後は \(V\ge3\) による。top rankは
\(c_2(G)\le\sum_{t\ge1}H_t/t\le S-\delta\le\delta(V-1)\)
なので (8.4) で払える。\(e\ge13\) では必要な \(V\ge3\) は成立する。\(\delta=0\) も両辺0のまま含まれる。

\(r=3\) なら \(a\ge6\)、従って \(\delta\ge6\) である。
\(H_1\le3\delta\) と各重みの \(t\ge2\) での上界から

\[
 \begin{aligned}
 c_1(G)-L_1&\le\frac{16}{3}\delta+\frac23S,
 \\
 c_2(G)-L_2&\le3\delta+\frac32S,
 \\
 c_3(G)&\le S-\delta.
 \end{aligned}
\]

第二式では \(W_2(1)=8/3\)、\(W_2(t)\le3/2\ (t\ge2)\) を用いた。\(e\ge13\)、\(\delta\ge6\) から \(V\ge29/2>13\) なので、それぞれ (8.4) の \(\delta(V+1)\)、\(2\delta(V+1)\)、\(\delta(V+1)\) 以下となる。

よって二本・三本のcutについて、別の歴史的閉鎖定理は要らない。

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

## 11 単一scalar不等式の証明

\(r\ge4\) の場合、\(\delta\ge a_r\ge10\) である。調和数を
\(\mathcal H_\delta=\sum_{u=1}^\delta1/u\) とし、cutoffを一律に \(D=\delta\) とする。

\[
 \alpha=\frac{r-1}{\delta+1},\quad
 B=1+(r-1)(\mathcal H_\delta-1)-\alpha(\delta-1),
 \quad c=\frac{r+1}{2}-\alpha>0.
\]

\(t\ge\delta\) の重みは \(\alpha\) 以下である。\(H_0=\delta\)、\(S\le\delta V\)、\(H_t\le M\) を使った上界は

\[
 U_r=\alpha\delta V+(r-1-\alpha)\delta+BM.
\]

さらに \(H_1\le M-a_r\) を同じ評価の中で使用すれば

\[
 F_r\le\widehat U_r:=U_r-ca_r. \tag{11.1}
\]

\(H_1\) を二度別の資源として消費したのではなく、\(U_r\) の \(H_1\) にかかる正の係数 \(c\) の上界を置き換えただけである。

### 11.1 rについての数値包絡

\(r_0=p(\delta)\) と置く。実際のcutは \(r\le r_0\) であり、\(\widehat U_r\le\widehat U_{r_0}\) である。

これを有限試験ではなく式で確認する。\(U_r=M+(r-1)K\) で、

\[
 K=\frac{\delta(V+\delta)}{\delta+1}
 +M\left(\mathcal H_\delta-2+\frac2{\delta+1}\right).
\]

\(\delta\ge10\)、\(e\ge2\) なら \(\mathcal H_\delta\ge2\)、\(V\ge(\delta+1)/2\)、\(M\ge\delta+1\) なので

\[
 K\ge\frac\delta2+\frac{\delta^2+2M}{\delta+1}>\frac32\delta.
\]

他方、\(c_r=(r+1)/2-(r-1)/(\delta+1)\) と書けば

\[
 c_ra_r-c_{r-1}a_{r-1}
 \le\frac{3r^2+r}{4}\le\frac32a_r\le\frac32\delta.
\]

したがって \(\widehat U_r\) は許される整数 \(r\) とともに増加する。
\(r_0>e-1\) の場合にも、これは単なる数値上界であり、その大きさのcutの存在は使わない。

### 11.2 二百本の無限e-ray

\(10\le\delta\le209\)、\(r=r_0\) に対し、

\[
 A_\delta=\delta+r-2-(r-1)\mathcal H_\delta-\alpha
\]

と置く。厳密なtarget差は

\[
 \widehat G(e,\delta)
 =\delta(V+1)-\widehat U_r
 =A_\delta(e+\delta-1)
 -\frac{\delta(\delta+r-2)}2+\delta\alpha+ca_r.
 \tag{11.2}
\]

これは \(e\) の一次式である。200個の各 \(\delta\) について、整数と有理数だけで

\[
 A_\delta>0,\qquad\widehat G(13,\delta)>0
\]

を検査すれば、**すべての \(e\ge13\)** が従う。

検算コードは [checks/verify_scalar.py](checks/verify_scalar.py)、200行すべての有理数は [certificates/scalar_e13.json](certificates/scalar_e13.json) にある。最小の初期差は \(\delta=45,r=9\) の

\[
 \frac{14727301309701473}{2950998796617300}>0,
\]

最小の傾きは \(\delta=10,r=4\) の \(27169/9240>0\) である。有限個の半群標本の試験ではなく、200本それぞれの無限rayを決める係数の確認である。

### 11.3 すべての大きい欠損への帰納

\(\delta\ge210\) では、改善前の \(U_r\) だけで十分である。
\(r_0=p(\delta)\ge20\) に対し、

\[
 \mathcal H_{a_r}\le\frac{r+4}{4}\quad(r\ge20)
\]

を示す。基底 \(\mathcal H_{210}<6\) は同じ有理数計算で確認する。
\(a_{r+1}-a_r=r+1\) なので

\[
 \mathcal H_{a_{r+1}}-\mathcal H_{a_r}
 \le\frac{r+1}{a_r+1}\le\frac14;
\]

最後は \(r^2-7r-6\ge0\) に等しく、\(r\ge20\) で成立する。

固定した \(r\ge20\) に対して

\[
 h_\delta=\frac{\delta+r-2}{2}-(r-1)\mathcal H_\delta
\]

は \(\delta\ge a_r\) で非減少である。実際、その前進差分は
\(1/2-(r-1)/(\delta+1)>0\) であり、基点では
\((a_r+r-2)/2=(r-1)(r+4)/4\) より \(h_{a_r}\ge0\) である。

未改善の差には恒等式

\[
 \delta(V+1)-U_r
 =(e-1)\left[\frac{\delta+r-2}{2}-\alpha\right]
 +(e+\delta-1)h_\delta
\]

がある。括弧は正なので、\(e\ge2\) で全差は非負となる。\(U_r\) は \(r\) とともに増加するから、数値包絡 \(r_0\) を使って実際のcutも払える。

これで \(e\ge13\)、\(r\ge4\) のすべてについて (10.2) が示された。

## 12 最後の組立て

任意のsourceを一つ取る。

1. 正規化幅 \(u=(g_e-m)/d<m\) なら、\(e\le7\) を境界補題B、\(e\ge8\) を境界補題Wで処理する。比較先は常に実際のcompletionのままである。proper narrow targetはすべてこの場合に入る。\(d>1\) では、この場合にも実際のtargetがordinaryになることがある。
2. \(u\ge m\) なら、物理幅 \(w=du\ge m\) なので、completionの実際の最小生成系は \(m,m+1,\ldots,2m-1\) である。\(e\le12\) は境界補題Bのordinary側を使う。\(e\ge13\) では、同じsourceに第4節のcutを一つ選ぶ。\(r=2,3\) は第9節、\(r\ge4\) は第10–11節によって同じcutの全 \(c_j(G)\le R_j\) を得る。第8節から全Betti行のP14が従う。

物理幅の境界 \(w=m-1\) はordinary targetを持つが、\(u<m\) なので第1の場合に含まれる。この順序ならBのうち、8〜12生成元の \(m>u\) 側の有限core計算は使わない。第0行は双方1であり、sourceの射影次元を超える行は0である。有限体への降下も第4節の通りである。

従って、明記した境界補題B、Wおよび公刊入力の下で、任意体・全total Betti行・実際のinterval completionに対するP14が成立する。□

## 13 Leanへ渡す最小の依存

形式化する鎖は次で足りる。

\[
 \text{数値座標}
 \longrightarrow\text{full-ring jump strataと実際の塔}
 \longrightarrow(H_0,H_1,S,\text{剰余占有上界})
 \longrightarrow\text{harmonic rank評価}
 \longrightarrow\text{単一scalar}
 \longrightarrow\text{ordinary target比較}.
\]

これに小生成元数Bと幅側Wを接続する。歴史的な全gateのregistry、巨大な既済領域の和集合、D16、E273、HEAD20、defect57、独立のtop-rank定理、4,086本のwaterfill経路は、この本文の最終組立てに不要である。

有限算術は200行の \(A_\delta>0\)、\(\widehat G(13,\delta)>0\) と \(\mathcal H_{210}<6\) をカーネルで証明すればよい。JSONのPASS値をLeanの根拠にしない。

先に自然数・有理数のscalar定理を形式化し、次に加群の条件付きrank定理を形式化する。その後に数値半群から条件を供給し、最後にB、Wを埋める。B、Wや公刊入力を未証明の `axiom` に置いた段階を、P14全体のLean完全証明と呼ばない。
