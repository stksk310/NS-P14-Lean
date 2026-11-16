# P14 全域証明の骨子 V03

2026年11月9日。今後の全文執筆に先立つ、主証明の構成・statement・接続式の確定稿。
V02の全文改稿、論文の完成、Lean形式認証を意味しない。

**採用する主ルートは一つである。ordinary側を同じcutのApéry塔とscalarで閉じ、
狭幅側をactual核を保った端点移行で閉じる。**
ordinaryの残部はApéry–Sidonと5行の表、N4の第一行は紙上の一括評価と少数の場合分けを使う。
旧第15節と196組証書、ナヴィのlex増分ルートは主証明に重ねない。

## この骨子の読み方

以下の各補題IDは [完全依存表](P14_DEPENDENCY_MAP_V03.md) と
lemma_registry.json のIDに一致する。各項目には、何を証明するか、適用範囲、
核心、次の接続、完全証明の所在を示す。証明の要点だけでは復元しにくい四つの橋は、
この骨子でも途中式を表示する。完全証明を省略した箇所を「監査済み」というラベルで代用しない。

~~~mermaid
flowchart TD
  T["主定理：actual completionとの全Betti比較"]
  T --> S["e≤3：直接計算・公刊三生成元定理"]
  T --> O["ordinary：w≥m−1"]
  T --> W["狭幅：w≤m−2, e≥4"]
  O --> A["数値Apéry・同jump strata・一つのcutと塔"]
  A --> K["harmonic Koszul → Tor → actual target"]
  K --> L["r=2,3：直接評価"]
  K --> M["r=4..8：Sidon＋5行scalar"]
  K --> H["r≥9：大rank評価"]
  W --> E["有限端点座標・全競合・actual核・Tor補償"]
  E --> G["e≥5：edge/dense/sparse/e=5構造"]
  E --> N["e=4：紙上N4＋全高次行＋幅4"]
~~~

矢印は読者が結論から根拠へ追う方向である。機械可読なdepends_onも同じ向きとし、
循環がないことを別途確認する。

## Part I 主定理、実際の比較対象、公刊入力

### I.1 主張と量化範囲

\(\Gamma=\langle m=g_1<\cdots<g_e\rangle\) を真正な最小生成系を持つ数値半群、
\(k\) を任意の体とする。
\[
G_\Gamma=\operatorname{gr}_{\mathfrak m}k[[t^\Gamma]],\qquad
\widetilde\Gamma=\langle m,m+1,\ldots,g_e\rangle.
\]
各環を、それぞれの最小生成系に対応する多項式環で表示してBetti数を取る。
主定理は
\[
\boxed{\beta_i(G_\Gamma;k)\le
       \beta_i(G_{\widetilde\Gamma};k)\qquad(i\ge0).}
\tag{V3-MAIN}
\]
同じ数の変数を無理に両辺へ加えて比較する主張ではない。
双方の第0行は1、sourceの \(i>e\) 行は0。
負の下添字・上添字を超える下添字の二項係数を0とする。

物理幅を \(w=g_e-m\) とする。\(e\ge2\) の場合だけ
\[
d=\gcd(g_2-m,\ldots,g_e-m),\qquad u=w/d
\]
を定める。\(e=1\) に空集合のgcdを適用しない。

### I.2 記号の局所範囲

| 領域 | 固定する記号 | 区別すべき量 |
|---|---|---|
|ordinary| \(\delta=m-e,\ M=m-1,\ \mathcal V=e+\delta/2-3/2\) | \(\mathcal V\) は資源係数で幅ではない |
|ordinary| \(r\) はcut本数、\(a=q_2\)、\(a_r=\binom{r+1}{2}\) | \(\delta\) を局所的に \(d\) と改名しない |
|ordinary| \(P=k[\lambda_1,\ldots,\lambda_r]\)、相対環 \(k[x,\lambda_1,\ldots,\lambda_r]\) | \(c_j\) は環を指定したTor交代和 |
|narrow| \(q=e-2,\ 0<a_1<\cdots<a_q<u,\ V_{\rm phys}=du\) | 実効target幅は \(\min(du,m-1)\) |
|narrow| \(Q_C=C/(x,v)C,\ Q_G=G/(x,v)G\) | endpoint変数 \(v\) とtarget幅を区別し、target幅は \(V_{\rm tar}\) とする |
|narrow| \(P_C=\dim Q_C,\ P_G=\dim Q_G,\ R=\dim(0:_G(x,v))\) | core商・actual商・actual socleを混同しない |
|幅4| \(m=4Q+\rho\) | 商 \(Q\) は内部変数数 \(q\) と区別する |

骨子中の引用式が旧記号を使うときは、その節の宣言を優先する。
論理的に別の量の同一視は行わない。

### I.3 Actual interval容量：I_TARGET

\(m\ge2\) とする。実効幅
\(V_{\rm tar}=\min(w,m-1)\) に対し、completionのatomは正確に
\(m,m+1,\ldots,m+V_{\rm tar}\)。
\[
D_{\rm tar}=V_{\rm tar}-((m-1)\bmod V_{\rm tar})
\in\{1,\ldots,V_{\rm tar}\}.
\]
算術列公式と接錐のBetti一致から、全 \(i\ge1\) で
\[
F_i(m,V_{\rm tar})
=i\binom{V_{\rm tar}}{i+1}+
\begin{cases}
(D_{\rm tar}+1-i)\binom{V_{\rm tar}}{i-1},&i\le D_{\rm tar},\\
(i-D_{\rm tar})\binom{V_{\rm tar}}i,&i>D_{\rm tar}.
\end{cases}
\tag{V3-TAR}
\]
\(i>V_{\rm tar}\) は0。剰余別最小容量
\[
F_i^{\min}(v)=i\binom v{i+1}
 +\min\left\{\binom v{i-1},\binom vi\right\}
\tag{V3-TMIN}
\]
は各行で \(v\) について非減少。
ordinaryでは \(V_{\rm tar}=m-1\) なので \(F_i=i\binom m{i+1}\)。
狭幅側はactual幅から \(F_i^{\min}(u)\) を引き出すだけで、
sourceやtargetを正規化した仮想半群に置き換えない。

**役割・接続。** ordinaryのtarget多項式、幅側の全行容量を一度だけ固定する。
完全証明は [V02 §1.3](/workspace/NS-P14-Lean/proof_integrated_v2/NS_P14_INTEGRATED_PROOF_JA.md:83)。

### I.4 公刊入力と基礎代数の境界

| ID | 使用する正確な入力 | 主ルートでの使用先 |
|---|---|---|
|X_GREEN|Green、次数2の超平面制限。Caviglia §1 (1.1)に再掲|ordinary cut|
|X_BHP_EK|BHP任意標数版とEK公式。Juhnke-Kubitzke–Venturello §2.2 Lemmas2–3|幅側dense lexのみ。旧ordinary lexへの辺は外す|
|X_KNESER|DeVos Theorem1のKneser和集合定理。合成数位数を含む|幅側距離和・N4|
|X_AP_BETTI|Gimenez–Sengupta–Srinivasan Theorem4.1|actual targetとW_EDGEの算術列source|
|X_AP_CONE|Herzog–Stamate Proposition2.5|actual targetとW_EDGEの算術列sourceの接錐一致|
|X_LTV|Lan–Tu–Vu Theorem1.1|真正な三生成元の全域比較|
|X_SC|Savchev–Chen §4 Theorem8|N4混合標準語|

原典リンクと正確な適用説明は
[V02 §1.2](/workspace/NS-P14-Lean/proof_integrated_v2/NS_P14_INTEGRATED_PROOF_JA.md:37)。
これらの定理を今回再証明したとはしない。

X_BASICはKoszul/Tor、Hilbert syzygy、rank Euler、有界spectral sequence、
同次Gröbner除法という通常の基礎代数である。
「任意商のBetti単調性」や「spectral sequenceの退化」は入力に含めない。

### I.5 任意体性：I_FIELD

一般一次形式を選ぶordinary cutの段階だけ、必要なら同標数の無限純超越拡大へ移る。
最小自由解消のflat base changeによりBetti数は元の体と等しく、最後に下降できる。
他の議論は各体上のKoszul複体、整数の単位minor、数値的な有理不等式で行う。
有理数の重みを評価に使うことは、基礎体内でその分母を割ることではない。
異なる標数のactual Betti数が等しいとは仮定しない。

**完全証明・接続。** V02 §4、§16。以下のO_CUTを正当化し、
狭幅側は各体上で直接進める。

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

## Part VI 全域合成、検証境界、全文執筆への接続

### VI.1 小生成元数：I_BASE、I_THREE

\(e=1\) なら数値半群は \(\mathbb N\) でありsourceとcompletionが等しい。
\(e=2\) なら \(\Gamma=\langle m,n\rangle,\ m<n,\ \gcd(m,n)=1\)、
\[
G_\Gamma\simeq k[x,y]/(y^m),\qquad
(\beta_0,\beta_1,\ldots)=(1,1,0,\ldots).
\]
これは \(y^m-x^n\) の最低次数項から従う。
completionの定義理想は非零なので第一行は少なくとも1であり、比較が成立する。

\(e=3\) はX_LTVを用いる。理想から商への添字換算と第0行1を含める。
ordinaryのcut2による別の証明も存在するが、全域合成では三生成元をこの一箇所で処理する。

**完全証明。** V02 §1.2(5)、§16。ここに旧第15節への依存はない。

### VI.2 境界を含む全域coverage：I_NORMALIZE、I_PARTITION

以下 \(e\ge4\) とする。整数幅 \(w\) は次の二つのどちらかを満たす。

| 領域 | 接続する仮定 | 適用先 |
|---|---|---|
|\(w\ge m-1\)|actual completionはordinary。\(2\le r\le e-1\)|O_CLOSE|
|\(w\le m-2,\ e=4\)|\(q=2,\ m\ge du+2,\ 0<a<b<u\)、gcd条件|N_CLOSE|
|\(w\le m-2,\ e\ge5\)|\(q=e-2\ge3,\ q+1\le u<m,\ m\ge du+2\)、gcd条件|W_CLOSE|

正規化では
\(d=\gcd(g_2-m,\ldots,g_e-m)\) とし、offsetを \(d\) で割る。
sourceの値・生成元は変えない。
\(\gcd(m,d)=1\) と正規化offsetのgcd1は数値半群のgcd1から従う。
幅境界 \(w=m-1\) はordinaryに含むので、未処理の整数幅はない。

ordinaryでは次の三分岐が全cutを覆う。
\[
\begin{array}{c|c|c}
r&追加条件&閉鎖補題\\ \hline
2,3&各低cutのactual条件&O_{\rm LOW}\\
4,\ldots,8&e\ge r+1,\ \delta\ge a_r&O_{\rm SMALL}\\
r\ge9&e\ge r+1\ge10,\ \delta\ge a_r&O_{\rm LARGE}
\end{array}
\]
O_SMALLでは \(r=6,7,8\) の負の基点をactual Apéry–Sidonで排除する。
\(r=2\) へ最大二次層の推論を適用しない。
\(\delta=0\) は空の塔としてO_LOWに含まれる。

狭幅では、W_CLOSEが最小幅・一欠落幅・dense・sparse・五生成元の端を処理し、
N_CLOSEが全正規化幅 \(u\ge3\)、全 \(d\ge1,m\ge du+2\) を処理する。
N4の第一行を新しくした後も、N_HIGHとN_WIDTH4を消さない。

### VI.3 全行・任意体の結論：I_MAIN

I_BASEとI_THREEにより \(e\le3\) が閉じる。
\(e\ge4\) ではVI.2の排他的な幅分割を行う。
ordinaryはO_CLOSE、狭幅の四生成元はN_CLOSE、五生成元以上はW_CLOSEで全行が閉じる。
O_TARGETおよびE_TRANSFERは後続spectral pageの次元減少を使うだけで退化を仮定せず、
actual targetの容量はI_TARGETに固定されている。
従って全source・全 \(i\ge0\) の(V3-MAIN)へ接続する。

sourceの上端 \(i=e\) は各閉鎖補題の範囲に含まれる。
\(i>e\) はHilbert syzygyによりsourceが0、第0行は双方1。
N4では特に \(i=4\) をN_HIGHで処理する。
最小幅でtargetの上端が低い場合も、W_EDGE又はN4の同一target/幅4処理が対応する。

任意体性はI_FIELDと、各補題の標数に依存しない証明を合わせる。
この段階で新たな有限半群の計算や、異なる標数のrank比較を追加する必要はない。

### VI.4 主証明に残る算術、外した歴史的依存

主ルートには、小さい有理数表、barrier恒等式、多項式係数の符号、
幅6–8の明示的な代数の場合分け、幅4の四剰余が残る。
それらは各数学的statementと証明の一部である。

旧196組・旧83組・665行比較・旧5tailの列挙証書は、主定理の必須依存から外れる。
コードが不要になったという意味ではなく、残すコードの役割は
定義式からの正確な算術検算と任意の回帰確認である。
有限回帰の成功から無限範囲を結論しない。

ナヴィの \(\Delta B_1\le m-2\) は独立した別証明として
[クロスレビュー](/workspace/NS-P14-Lean/navi_cross_review/NAVI_CROSS_REVIEW_JA.md) に保存する。
それはfirst-hit/truncated lexを保持するため、この主DAGには辺を加えない。

### VI.5 今回固定するものと、次の全文執筆で行うもの

今回固定するのは、各補題の量化範囲、依存、完全証明の所在、四つの橋の途中式、
全域coverage、および内部監査と形式認証の区別である。
単一骨子が完成しても、各公刊定理や共通代数をLean kernelが確認したことにはならない。

次の全文執筆では、この順序で完全証明を移し、局所記号を統一し、
旧節番号から新しい補題番号への参照を一度だけ更新する。
旧稿を切り貼りして不要な旧証書の必須参照を残すことは避ける。
監査課題と形式化の範囲は
[査読準備表](P14_REFEREE_READINESS_V03.md)、
移動・保持・置換は
[置換台帳](P14_PROOF_REPLACEMENT_LEDGER_V03.md) に記録する。
