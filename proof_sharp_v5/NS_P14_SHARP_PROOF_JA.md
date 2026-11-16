# NS-P14：簡約された全域証明 V05

読解基準：work commit `345e2d82fea50ef89e00a8f35c4fb53ac601d7ce`。
本稿は公刊入力を引用する紙上証明である。既存Leanとの対応、
新しい紙上補題、形式化の未到達範囲は別冊の変更台帳に記録する。
全体の論証に必要な付録はなく、今回固有の補題は以下に展開する。

# 1 主張、公刊入力、actual sourceとtargetへの共通接続

## 1.1 比較する対象と規約

数値半群 \(S=\langle m=g_1<\cdots<g_e\rangle\) の生成系は最小とする。
任意の体 \(k\) に対し
\[
G_S=\operatorname{gr}_{\mathfrak m}k[[t^S]],\qquad
\widetilde S=\langle m,m+1,\ldots,g_e\rangle
\]
とおく。\(\beta_i(G_S;k)\) は \(k[X_1,\ldots,X_e]\) 上の商としてのtotal Betti数である。
targetの表示にはtarget自身の最小生成元を使う。証明する主張は
\[
\boxed{\beta_i(G_S;k)\le\beta_i(G_{\widetilde S};k)\quad(i\ge0).}\tag{MAIN}
\]
負の下添字、または上添字を超える下添字の二項係数は0とする。切上げ・床・差は
整数または有理数で先に解釈する。自然数上の飽和減算を整数減算と取り違えない。
有理重みは数値的な不等式の係数であり、体 \(k\) 内の除法を意味しない。

## 1.2 使用する公刊入力

以下は通常の数学的引用である。各入力の一般的再証明を本論へ重ねない。

| 入力 | 使用する版・仮定・結論 | 適用箇所 |
|---|---|---|
| Green | 無限体上の標準次数付き代数の次数2超平面制限。Macaulay下降による上界。Caviglia, *A hyperplane restriction theorem and applications to reductions of ideals*, §1 (1.1) に再掲された任意標数版 | ordinaryの一つのcut |
| BHP・EK | 同じ全Hilbert関数を持つlex商が任意の斉次商の各graded Betti数を抑える。lex理想の極小単項式 \(v\) は商の第 \(i\) 行に \(\binom{\max(v)-1}{i-1}\) を寄与。Juhnke-Kubitzke–Venturello, §2.2 Lemmas 2–3。Pardueの正標数版を含む | dense幅の一つのlex商 |
| Kneser | 有限非空 \(A,B\) と \(H=\operatorname{stab}(A+B)\) に対し \(|A+B|\ge|A+H|+|B+H|-|H|\)。DeVos, Theorem 1。合成数位数を許す | 巡回群の距離・体積 |
| 算術列Betti公式 | Gimenez–Sengupta–Srinivasan, arXiv:1108.3203, Theorem 4.1。最小算術列生成系、任意体 | interval targetとfull AP source |
| 算術列接錐一致 | Herzog–Stamate, arXiv:1308.4644v3, Proposition 2.5。算術列半群環とその接錐のtotal Betti一致 | 同上 |
| LTV | Lan–Tu–Vu, arXiv:2307.05589v1, Theorem 1.1。三生成元・任意体の接錐のBetti比較。理想の添字は商で一つずらす | \(e=3\) |
| Savchev–Chen | *Long zero-free sequences in finite cyclic groups*, §4 Theorem 8。位数 \(u\) の巡回群の零和自由列が長さ \(>u/2\) なら、あるunitを掛けた正代表の総和を \(<u\) にできる | N4混合標準語 |

原典URLはそれぞれ
[Green再掲](https://www.math.purdue.edu/~gcavigli/Articles-PDF/%5BS4%5D.pdf)、
[BHP・EK再掲](https://link.springer.com/article/10.1007/s40306-021-00449-8)、
[Kneser](https://www.sfu.ca/~mdevos/papers/kneser.pdf)、
[算術列公式](https://arxiv.org/pdf/1108.3203)、
[算術列接錐](https://arxiv.org/pdf/1308.4644)、
[LTV](https://arxiv.org/html/2307.05589v1#S1)、
[SC](https://arxiv.org/html/math/0602568v1) である。
この版の登録は既存原稿と照合したもので、原典全文の新たな独立再査読とは区別する。
Koszul複体、Tor長完全列、Hilbert syzygy、rank Euler、収束する有界二重複体の
spectral sequence、同次Gröbner除法は通常の基礎代数として用いる。

## 1.3 共通接続補題 BRIDGE

**補題 BRIDGE.** 次の四つの接続は、以後すべての分岐に共通である。

(a) \(k[t^S]\) の正元単項式イデアルによる代数的接錐と \(G_S\) は、
各原子の初期形を保つ次数付き \(k\)-代数同型で結ばれる。従って同じ最小表示でBetti数が等しい。

(b) 同標数の体拡大で、sourceとtargetの各Betti数は変わらない。

(c) \(e\ge4\)、\(w=g_e-m\le m-2\) とし
\[
d=\gcd(g_2-m,\ldots,g_e-m),\quad u=w/d,\quad q=e-2
\]
とおく。元のsourceを保ったまま
\[
S=\langle m,m+da_1,\ldots,m+da_q,m+du\rangle,
\quad0<a_1<\cdots<a_q<u,
\]
\[
\gcd(a_1,\ldots,a_q,u)=\gcd(m,d)=1,\qquad
q+1\le u,\qquad m\ge du+2
\tag{NORMAL}
\]
という端点データを得る。物理幅は \(du\) であって \(u\) ではない。

(d) targetの容量 \(F_i(m,v)\) を次節の式で定める。
狭幅で \(u\ge i\ge1\) かつ \(\beta_i(G_S;k)\le F_i^{\min}(u)\) を示せば
\(\beta_i(G_S;k)\le\beta_i(G_{\widetilde S};k)\) となる。
この容量法で閉じない最小幅の枝には、source=target又は物理幅での直接比較を使う。
各枝が正行 \(1\le i\le e\) を閉じれば、第0行と \(i>e\) を一度だけ補って (MAIN) を得る。

**証明.** \(s\in S\) のorderを、原子による表示の最大長とする。
次数 \(n\) のイデアル冪は、orderが \(n\) 以上の指数をsupportに持つ。
代数的環では有限和、完備環では形式和である。後者の主張も、有限個の長さ \(n\) の
原子積で割れる各指数を、一つ選んだその積に振り分ければ、その有限個の積を係数形式級数に
掛けた和になることから従う。各級の商にはorderが正確に \(n\) の単項式だけが残る。
その指数は有限個である。実際、各剰余類のApéry元を \(b\) とすると
\(s=b+\ell m\) であり、orderが \(n\) なら \(\ell\le n\) である。
両環の各級は従って同じ有限基底を持つ。積は両側ともorderが加法的な場合だけ生存するため一致し、
全級の同型は原子初期形と表示環の作用を保つ。これが(a)である。

体拡大 \(K/k\) に最小次数付き自由解消をtensorすると、flatnessにより解消のままで、
微分の係数が斉次極大イデアルに入るという最小性も残る。そのrankは変わらない。
(a)又は同じ単項式座標で接錐のbase changeも同定できるから(b)を得る。
一般cutが必要なときだけ無限純超越拡大を選び、最後にこの等式で戻る。

(c)のoffsetは相異なる正整数なので、その最大値を \(d\) で割ると表示の形を得る。
\(d\) の定義から正規化offsetのgcdは1である。また
\(\gcd(m,d)=\gcd(g_1,\ldots,g_e)=1\)。内部の \(q\) 個の整数は
\(1,\ldots,u-1\) に入るので \(q+1\le u\)。狭幅仮定が \(m\ge du+2\) を与える。
生成元の値は変えていないため、これは元のsourceの記述である。

(d)では実target幅は \(v=du\ge u\)。次節で示す容量単調性から
\(F_i^{\min}(u)\le F_i^{\min}(du)\le F_i(m,du)\) となる。
第0行は両側1。sourceは \(e\) 変数多項式環の有限生成商なので \(i>e\) のBetti数は0である。
sourceが消えるときtargetも消えるとは要求しない。\(\square\)

## 1.4 actual interval容量を一度だけ固定する

\(m\ge2\) とする。このとき \(e\ge2,w\ge1\) なので \(v=\min(w,m-1)\ge1\) である。
\(\widetilde S\) の最小生成系は
正確に \(m,m+1,\ldots,m+v\)。\(w<m-1\) なら全て \(<2m\) なので分解できない。
\(w\ge m-1\) なら \(m,\ldots,2m-1\) が全ての \(n\ge m\) を帰納的に生成するため、
それ以上の生成元は不要である。

\(D=v-((m-1)\bmod v)\in\{1,\ldots,v\}\) とする。算術列公式と接錐一致から
\[
\beta_i(G_{\widetilde S};k)=F_i(m,v)
=i\binom v{i+1}+
\begin{cases}
(D+1-i)\binom v{i-1},&i\le D,\\
(i-D)\binom vi,&i>D
\end{cases}\quad(i\ge1).
\tag{CAP}
\]
\(i>v\) では0である。原公式の \(m=av+b,\ 1\le b\le v\) に対して
\(D=v-b+1\) と置き、理想の解消から商へ添字を一つずらした形が (CAP) である。

\(1\le i\le v\) で剰余パラメータの最小値は
\[
F_i^{\min}(v)=i\binom v{i+1}+
\min\left\{\binom v{i-1},\binom vi\right\}.
\tag{MINCAP}
\]
実際、\(D\ge i\) の側は \(D=i\)、\(D<i\) の側は \(D=i-1\) で最小となる。
端 \(i=1\) では前者だけ、\(i=v\ge2\) では後者の値1が最小で、同じ式になる。
\(v=i=1\) は唯一の \(D=1\) を直接代入して同じ値1を得る。
固定した \(i\) に対して各二項係数は \(v\) とともに非減少なので、(MINCAP) も非減少である。
\(v<i\) の領域にはこの最小式を適用せず、actual容量0を使う。

ordinaryの \(v=m-1,D=v\) では、Pascal恒等式により
\[
F_i(m,m-1)=i\binom m{i+1}.\tag{ORDCAP}
\]
幅側で用いる下界は
\[
\begin{aligned}
F_1&\ge\binom v2+1,& F_2&\ge2\binom v3+v\quad(v\ge3),\\
F_3&\ge3\binom v4+\binom v2\quad(v\ge5),& F_4&\ge4\binom v5.
\end{aligned}
\tag{LOWCAP}
\]
各下界は (MINCAP) で二候補の小さい方を選ぶだけである。特に第3行の
\(v\ge5\) を幅4へ延長しない。


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


# 4　五生成元以上の狭幅比較

本章の仮定は、元の半群を表す端点データ
\[
 \begin{gathered}
 S=\langle m,m+da_1,\ldots,m+da_q,m+du\rangle,\\
 e=q+2\ge5,\quad0<a_1<\cdots<a_q<u,\quad m\ge du+2.
 \end{gathered}
\]
である。正規化はこの表示の座標選択である。以下の資源はすべて、この同じ元の向きのデータから取る：
\[
 \begin{gathered}
 P=P_C=\dim_k Q_C,\quad W=1+\sum_{r\bmod u}\ell_r,\\
 R=\dim_k(0:_G(x,v)),\quad
 \widehat R=\min\{W-u,u\max(H_x-2,0)\}.
 \end{gathered}
\]
端点章から \(P\le W\)、\(R\le\widehat R\) と次の二式を使う。
\[
 \beta_i(G)\le b_i(Q_C)+P\binom q{i-1}
                       +R\binom{q+1}{i-1},                 \tag{W-T}
\]
\[
 \beta_i(G)+\binom{q+1}{i+1}
 \le P\binom{q+1}i+\widehat R\binom{q+1}{i-1}
 \qquad(i\ge1).                                       \tag{W-G}
\]
後者は減算を伴わない形で用いる。\(P_C=P_G\) や任意の商のBetti単調性は仮定しない。
共通接続補題により、各正行を
\[
 F_i^-(u)=i\binom u{i+1}
       +\min\left\{\binom u{i-1},\binom ui\right\}       \tag{W-F}
\]
以下に抑えれば、物理幅 \(du\ge u\) の literal interval completion が支払う。
例外は完全算術列の \(d=1\) で、そこでの支払いはsourceとtargetの一致を使う。
二項係数は整数添字で範囲外を0とする。以下は \(1\le i\le e\) を扱えばよく、
第0行と \(i>e\) は共通接続補題で処理する。

## 4.1　端の二幅

### W-AP　完全算術列 \(u=q+1\)

内部offsetを全部含むのでsourceは算術列である。算術列の任意体上の接錐公式は
\[
 \beta_i=i\binom u{i+1}+
 \begin{cases}(c+1-i)\binom u{i-1},&i\le c,\\
 (i-c)\binom ui,&i>c,\end{cases}\qquad1\le c\le u.
\]
補正は前者では \((u+1-i)\binom u{i-1}=i\binom ui\) 以下、
後者でも \(i\binom ui\) 以下だから、\(\beta_i\le i\binom{u+1}{i+1}\)。
\(d\ge2\) なら \(du\ge2u\ge u+1\) でtargetの第一項が払う。
\(d=1\) ならsourceの生成集合自体が \(\{m,m+1,\ldots,m+u\}\) であり、
literal targetと同一の半群である。ここでは \(F_i^-(u)\) による支払いを要求しない。□

### W-HOLE　一欠落幅 \(u=q+2\)

欠落offsetを \(h\)、\(B=\{0,1,\ldots,u\}\setminus\{h\}\) とする。
整数コアの次数 \(n\) の基底は
\[
 nB\setminus\bigl((n-1)B\cup((n-1)B+u)\bigr).           \tag{W-H1}
\]
これは同次数・同offsetの単項式を一つにした基底から、端点倍を除いたものである。
\(2\le h\le u-2\) では \(B+B=[0,2u]\)：欠け得る二点 \(h,h+u\) は
\(1+(h-1)\)、\((u-1)+(h+1)\) で表される。
よって
\[
 \begin{gathered}
 h_0=1,\quad h_1=q,\quad (Q_C)_2=kz_-\oplus kz_+,\\
 z_-=(2,h),\quad z_+=(2,h+u),\quad h_n=0\ (n\ge3).
 \end{gathered}
                                                                  \tag{W-H2}
\]
実際 \((B+B)\cup(B+B+u)=[0,3u]\) が次数3を消し、標準次数付き性がその先も消す。
\(h=1\) なら \(B+B=\{0\}\cup[2,2u]\)、
\((B+B)\cup(B+B+u)=\{0\}\cup[2,3u]\supset3B\) だから、唯一の二次基底は \((2,u+1)\)。
\(h=u-1\) のコア基底は \((n,b)\mapsto(n,nu-b)\) で得られ、唯一の二次基底は \((2,u-1)\)。
この反射はコアの基底を数えるためだけに使う。すべての基底を**元の向き**で評価すると
\(L=n-\lceil b/u\rceil\le1\) であり、\(H_x\le1\)、従って \(R=\widehat R=0\) である。
また \(P=q+3\)（内部欠落）、\(P=q+2\)（端欠落）となる。

内部欠落では一次元空間を二ブロック \(U\oplus Z\) に分け、
\(r=h-1\)、\(s=u-h-1\)、\(r+s=q\)、\(r,s\ge1\) と書く。
積が非零なのは、\(U\) 内で \(a+b=h\) のとき \(z_-\)、
\(Z\) 内で \(a+b=h+u\) のとき \(z_+\) の場合だけである。
各ブロックの乗法行列は置換行列で、平方項も係数1を持つ。
Koszul微分の一次から二次への部分
\[
 D_i:(U\oplus Z)\otimes\bigwedge^i(U\oplus Z)
       \longrightarrow(kz_-\oplus kz_+)\otimes\bigwedge^{i-1}(U\oplus Z)
\]
を考える。行 \(z_-\otimes e_J\) が非零である条件は \(U\not\subseteq J\)。
\(a\in U\setminus J\) を選ぶと、その乗法双対 \(a^*\) の列
\(a^*\otimes e_{J\cup\{a\}}\) はこの行だけに \(\pm1\) を持つ。
第二ブロックでも同じ選択を行う。異なる行に選んだ列が同一なら非零の行も同一になるため、
元の整数行列に対角 \(\pm1\) のminorが得られる。零行数と合わせて
\[
 \rho_i=\operatorname{rank}D_i
   =2\binom q{i-1}-\binom s{i-1-r}-\binom r{i-1-s}.     \tag{W-H3}
\]
次数0から1への微分にも、各wedgeの最小変数を選ぶ単位minorがあり、rankは \(\binom qi\)。
従ってchain次元から前後のrankを引き、Pascal恒等式で整理すると
\[
 b_i(Q_C)=i\binom{q+1}{i+1}-2\binom q{i-1}+T_i,
 \quad T_i=\binom{s+1}{i-r}+\binom{r+1}{i-s}.           \tag{W-H4}
\]
これは範囲外の \(b_i=0\) も含む全正行で有効である。
対角係数は \(\pm1\) なので、標数2でもrankの根拠が保たれる。

必要な二つの補正評価を、単射で一度に記録する：
\[
 T_i\le\binom{q+2}i,\qquad T_i\le\binom{q+2}{i-1}.      \tag{W-H5}
\]
第一式では互いに素な \(U,Z\) と追加二点 \(a,b\) を取り、
\(D\subset Z\cup\{a\}\)、\(|D|=i-r\) を \(U\cup D\) に、
\(E\subset U\cup\{b\}\)、\(|E|=i-s\) を \(Z\cup E\) に送る。
衝突は \(i=q\) の \(U\cup Z\) の二コピーだけである。
固定した \(u_0\in U,z_0\in Z\) に対し第二コピーを
\((U\setminus\{u_0\})\cup(Z\setminus\{z_0\})\cup\{a,b\}\) に移すと単射になる。
第二式では \(k=q+1-i\) とし、\(k<0\) は \(T_i=0\)。
それ以外では \(T_i=\binom{r+1}k+\binom{s+1}k\)。
大きさ \(r+1,s+1\) の互いに素な二集合に各二点を固定し、
一方の \(k\) 元部分集合に反対側の固定二点を足す。
衝突は \(k=2\) の四固定点だけである。
\(q\ge3\) だから一方の集合は三点以上を含み、第二コピーをその側の三点と他方の一点の集合へ移せる。
得られる像は \(k+2\) 元集合で、その総数は \(\binom{q+2}{k+2}=\binom{q+2}{i-1}\)。

(W-T) と \(P=q+3,R=0\) を (W-H4) に代入し、
\(i\binom{q+1}i=(q+1)\binom q{i-1}\) を使うと、target下界との差は正確に
\(\min\{\binom{q+2}{i-1},\binom{q+2}i\}-T_i\ge0\) となる。
端欠落では一つの置換フォームだけが残り、同じminorから
\(\rho_i=\binom q{i-1}\ (1\le i\le q)\)、\(\rho_{q+1}=0\) となる。
\(P=q+2\) を使う同じchain計算は
\[
 \beta_i(G)\le i\binom{q+2}{i+1}
                  +\mathbf1_{i=q}+\mathbf1_{i=q+1}.     \tag{W-H6}
\]
二つの指示関数の現れる行では、target最小補正がそれぞれ1以上である。
上端 \(i=q+1\) の指示関数も保持した。□

## 4.2　密幅：一つのlex商と一つの容量差

### W-DENSE　\(q\ge4\)、\(u=q+1+t\)、\(2\le t\le q\)

まず以下の資源証明は \(q\ge3,0\le t\le q\) でも有効である。
生存内部語の長さを \(n\) とする。長さ \(l\ge2\) の部分語の剰余が既存offset \(a\) なら、
そのoffset和は \(a+cu\)、\(0\le c\le l-1\) であり、coreで
\(x^{l-c-1}v^cy_a\) という端点因子を持つ語に等しい。剰余0の場合も
\(x^{l-c}v^c\)、\(1\le c\le l-1\) に等しい。どちらも \(Q_C\) では0である。
従って長さ2から \(n\) のprefixはすべて欠落剰余を持つ。
二つが同じ剰余なら間の部分語が零和となり、その長さが1なら内部offsetの範囲に矛盾、
2以上なら今の議論に矛盾する。ゆえに \(n-1\le t\)、元の向きの \(H_x\le t\)。
\(A=\{0,a_1,\ldots,a_q\}\) は \(|A|=q+1>u/2\) なので、
任意の \(r\) に対して \(A\cap(r-A)\ne\varnothing\)。
既存剰余の最短長は1、欠落剰余の最短長は2であるから
\[
 W=q+1+2t,\quad P\le q+1+2t,\quad
 R\le\widehat R\le t,\qquad t\le2\Longrightarrow R=\widehat R=0.
                                                               \tag{W-D1}
\]

同じ**全Hilbert関数**を持つ一つのlex商 \(T/L\) を選ぶ。
lex理想はstrongly stableであり、大きい添字の因子を小さい添字へ替えても理想内にある。
\(S_j(n)\) を最初の \(j\) 変数内に支持される次数 \(n\) の標準単項式数とし、
\(S_0(n)=0\ (n>0)\)、\(S_q(n)=h_n\)、\(S_j(1)=j\) とする。
最大変数が \(y_j\) の次数 \(n\) の極小生成元数は
\[
 g_j(n)=S_j(n-1)-S_j(n)+S_{j-1}(n).
\]
実際、idealのshadow中の最大変数 \(y_j\) の単項式は、その \(y_j\) を除いた
前次数のidealの最初の \(j\) 変数内の単項式と一対一に対応する。
標準単項式数を差し引いてこの式を得る。
Artin性による次数方向のtelescopingと、任意標数のBHP上界およびstable idealのEK公式は
\[
 b_i(Q_C)\le i\binom{q+1}{i+1}+K\binom{q-1}{i-1},
 \quad K=\sum_{n\ge2}\sum_{j=1}^qS_{j-1}(n)             \tag{W-D2}
\]
を与える。第一項には \(\sum_{j=1}^qj\binom{j-1}{i-1}=i\binom{q+1}{i+1}\) を使った。

\(r\le q\) と \(\binom{r+1}2\ge2t\) を満たす \(r\) を選ぶと、
\(\sum_{n\ge2}h_n=P-1-q\le2t\) だから、高次lex標準語は末尾 \(r\) 変数に支持される。
その変数だけの次数 \(n\) 単項式は \(\binom{n+r-1}n\ge\binom{r+1}2\ge h_n\) 個あり、
外の変数を含む単項式より辞書順で小さいためである。
次数 \(n+1\) の単項式で全直接除数が次数 \(n\) の標準集合に入るものを子と呼ぶ。
子の最大変数を除く写像は、最初の \(j\) 変数内の標準親への全単射を与える。
逆写像では最大変数を掛け、他の直接除数は元の親より辞書順で小さいから標準である。
よって子数 \(M_n\) は \(\sum_jS_j(n)\)、\(M_n-h_n=\sum_jS_{j-1}(n)\)。
親子incidenceの重みを「除く変数の、子での指数」とすると、各子の総重みは \(n+1\)、
各親から末尾 \(r\) 変数内の候補子への総重みは \(n+r\) である。従って
\[
 K\le\sum_{n\ge2}\frac{r-1}{n+1}h_n\le\frac{2t(r-1)}3. \tag{W-D3}
\]
これは有限整数集合の有理重み計数であり、係数体で除法していない。

容量の差を固定する。\(A_i=\binom{q-1}{i-1}\)、\(C_i=\binom q{i-1}\)、
\(B_i=\binom{q+1}{i-1}\) とし、
\[
 \mathscr D_i=i\left[\binom{q+t+1}{i+1}-\binom{q+1}{i+1}\right]
              -(q+1+2t)C_i-RB_i-KA_i.                 \tag{W-D4}
\]
Vandermondeの最初の二つの正項から
\[
 i\left[\binom{q+t+1}{i+1}-\binom{q+1}{i+1}\right]
 \ge t(q+1)C_i+i\binom t2B_i.                          \tag{W-D5}
\]
\(t=2\) は \(r=3\)、\(K\le\lfloor8/3\rfloor=2\)、\(R=0\) として、
\(\mathscr D_i\ge(q-3)C_i+iB_i-2A_i\ge0\)。
\(q-3\ge1\)、\(i\ge1\)、\(C_i,B_i\ge A_i\) による。
\(t=3\) は \(r=3\)、\(K\le4\)、\(R\le3\) として、
\(\mathscr D_i\ge(2q-4)C_i+(3i-3)B_i-4A_i\ge0\)。
\(4\le t\le q\) なら \(r=t\)、\(K\le2t(t-1)/3\)、\(R\le t\) である。
\(i\binom t2-t\ge t(t-3)/2\ge0\)、\(B_i\ge C_i\ge A_i\) から
\[
 \mathscr D_i\ge
 \left[\frac{5t^2-17t-6}{6}+(t-1)(q-t)\right]C_i\ge0.
\]
最後は \(t=4+z,q=t+v\) としたとき、括弧の6倍が
\(5z^2+23z+6+6zv+18v>0\) となることによる。
(W-T)、(W-D1–2) により、全正行で \(\beta_i(G)\le i\binom u{i+1}\) が従う。□

## 4.3　共通の高次行補題と疎幅

### W-HIGH　第二行から全高次行への移行

**補題。** 整数 \(e\ge2,u\ge e\) と有理数 \(B\) に対し
\[
 U_i(B)=B\binom ei-u\binom{e-1}{i-1}-\binom{e-1}{i+1}
 \qquad(2\le i\le e)                                 \tag{W-HIGH1}
\]
と置く。\(U_2(B)\le2\binom u3\) なら、全 \(2\le i\le e\) で
\(U_i(B)\le i\binom u{i+1}\) が成り立つ。
特に \(e=q+2\) の端点データが (W-G) と
\(P\le B,\widehat R\le B-u\) を満たせば、第二行のこの数値比較だけで
\(\beta_i(G)\le i\binom u{i+1}\ (2\le i\le e)\) を得る。

**証明。** 正の整数 \(\binom ei\) で割った容量を
\[
 \mathcal T_i(u)
 =\frac{i\binom u{i+1}+u\binom{e-1}{i-1}+\binom{e-1}{i+1}}{\binom ei}
                                                        \tag{W-HIGH2}
\]
とする。
\(U_i(B)\le i\binom u{i+1}\) は \(B\le\mathcal T_i(u)\) と同値。
Pascal恒等式と二項係数の隣接式から、基点と幅1の増分は
\[
 \mathcal T_i(e)=e-1+i/e,\qquad
 \mathcal T_i(u+1)-\mathcal T_i(u)
       =i\frac{\binom ui}{\binom ei}+i/e.              \tag{W-HIGH3}
\]
\(u\ge e\) で比 \(\binom ui/\binom ei\) の隣接比は
\((u-i)/(e-i)\ge1\ (i<e)\)。従って基点も各増分も \(i\) に関して非減少であり、
幅に関する帰納法により \(\mathcal T_i(u)\ge\mathcal T_2(u)\ge B\) を得る。
隣接比を使うのは \(i<e\) のときだけで、top \(i=e\) で \(e-i\) による除法は行わない。

端点データへの適用では、(W-G) と二つの資源上界から
\[
 \begin{aligned}
 \beta_i(G)
 &\le B\binom{e-1}i+(B-u)\binom{e-1}{i-1}-\binom{e-1}{i+1}\\
 &=U_i(B)
 \end{aligned}
\]
となる。最後の等式はPascal恒等式であり、同じ \(B\) を全行に使う。□

### W-SPARSE　\(e\ge6\)、\(u\ge2e-2\)

まず (W-S1)–(W-S2) は \(e\ge5,u\ge e-1\) で成立する一般資源として証明する。
疎幅の追加条件による支払いは (W-S3) 以後で行う。
\(a=e-1\)、\(s=\lceil a/2\rceil=\lfloor e/2\rfloor\) と置く。
\(A=\{0,a_1,\ldots,a_q\}\) は巡回群を生成する \(a\) 元集合である。
\((n+1)A\) が全群でなければ、Kneserのstabilizer \(H\) は真部分群であり、
\(A+H\) のcoset数 \(c\) は \(c\ge2,c|H|\ge a\) を満たす。
Kneserから増分は \((c-1)|H|\ge c|H|/2\ge a/2\)、従って少なくとも \(s\)。
ゆえに
\[
 |nA|\ge\min(u,a+(n-1)s)\quad(n\ge1),\quad
 W\le B(u):=u+\sum_{j\ge0}(u-a-sj)_+.                 \tag{W-S1}
\]
この議論は合成数の \(u\) も含む。\(0\in A\) なので、最短長の各層を数える恒等式
\(W=u+\sum_{n\ge1}(u-|nA|)\) が後半を与える。
\(\Delta=u-a=sk+b\)、\(0\le b<s\) とすれば、等差数列の和により
\[
 B=u+\frac{\Delta^2}{2s}+\frac\Delta2+\frac{b(s-b)}{2s}
 \le B_*:=u+\frac{\Delta^2}{2s}+\frac\Delta2+
                    \frac{\lfloor s^2/4\rfloor}{2s},
 \qquad B\le\frac{u^2}{a}.                            \tag{W-S2}
\]
最後の差は
\[
 2(u^2-aB)=s(2s-a)k^2+ask+2(2s-a)kb+2b^2\ge0,
\]
と展開される。ここで \(2s\ge a\) を用いた。

端点章の二つの第一行調和評価と (W-T) は、同じ資源 \(P\le B,R\le B-u\) から
\[
 \beta_1(G)\le\frac{e+3}{3}B-u+\frac{e(e-1)}6,
 \qquad
 \beta_1(G)\le\frac{e+5}{4}B-u+\frac{(e-1)e(e+1)}{24}.  \tag{W-S3}
\]
\(e=6,7,8,9\) は第二式を使う。\(z=u-(2e-2)\ge0\) とすると、
\(\binom u2+1\) から第二式の \(B=B_*\) の右辺を引いた差は次の恒等式である。

| \(e\) | \(B_*\) | 容量差 |
|---:|---|---|
|6|\((u^2-u+12)/6\)|\(z^2/24+43z/24+1/2\)|
|7|\((u^2-3u+20)/6\)|\(2z+1\)|
|8|\((u^2-2u+25)/8\)|\(3z^2/32+63z/16+211/32\)|
|9|\((u^2-4u+36)/8\)|\(z^2/16+17z/4+29/4\)|

\(e\ge10\) は第一式と \(B\le u^2/(e-1)\) を使い、同じ差は
\[
 \frac{(e-1)(e-10)}2+1+\frac{4e-33}{6}z
                  +\frac{e-9}{6(e-1)}z^2>0.           \tag{W-S4}
\]
これらは有限例の検算でなく、全 \(z\ge0\) に対する係数表示である。

高次行には W-HIGH を、同じ資源上界 \(B=B(u)\) で適用する。
\(P\le B,\widehat R\le B-u\) はすでに得られたので、必要なのは第二行だけである。
\(B\le u^2/(e-1)\) を \(U_2(B)\) に代入すると
\[
 2\binom u3-U_2(B)\ge
 \frac u6\{2u^2-(3e+6)u+6e-2\}+\binom{e-1}3.          \tag{W-S6}
\]
\(e\ge7\) は \(e=7+v,u=2e-2+z\)、\(v,z\ge0\) として、括弧が
\[
 2v^2+5vz+12v+2z^2+21z+4>0.                           \tag{W-S7}
\]
これで従来の \(e=7\) と \(e\ge8\) の枝を統合する。
\(e=6,u\ge10\) は (W-S6) の右辺そのものが
\((u-10)(u-3)(u+1)/3\ge0\)。
これで第二行が閉じ、W-HIGH により上端を含む全 \(2\le i\le e\) が閉じる。□

## 4.4　五生成元：十分な上界だけで閉じる

### W-FIVE-SMALL　\(q=3,u=6,7\)

(W-D1) から \(u=6\) では \(P\le8,\widehat R=0\)、\(u=7\) では \(P\le10,\widehat R\le3\)。
第一行の調和評価は \(b_1\le2P/3+10/3\) である。
\(u=6\) では整数性により \(b_1\le8\)、従って \(\beta_1\le16=\binom62+1\)。
\(u=7,R=0\) では \(b_1\le10\) から \(\beta_1\le20\)。
\(R>0\) の場合だけ、元の \(H_x\ge3\) が必要となる。
剰余0の極小点は \((0,0)\) だけなので、このheightは非零剰余の極小点から来る。
その次数は \(L+K+1\ge4\) であり、\(\tau=\sum_{n\ge3}h_n\ge1\)。
調和和の次数2の係数を \(2/3\)、次数3以上の係数を \(1/2\) 以下として
\[
 b_1\le6+\tfrac23(P-4)-\tfrac16\tau\le10-\tfrac16<10.
\]
整数性から \(b_1\le9\)、(W-T) から \(\beta_1\le9+10+3=22=\binom72+1\)。
この \(b_1\le9\) を \(R=0\) の枝へ無条件に拡張していない。

高次行は (W-G) の同じ行パッケージを使えば十分である：
\[
 \beta_2+4\le6P+4\widehat R,\quad
 \beta_3+1\le4P+6\widehat R,\quad
 \beta_4\le P+4\widehat R,\quad\beta_5\le\widehat R.    \tag{W-5G}
\]

| \(u\) | 第2–5行の十分な上界 | \(F_2^-,F_3^-,F_4^-,F_5^-\) |
|---:|---|---|
|6|\((44,31,8,0)\)|\((46,60,39,11)\)|
|7|\((68,57,22,3)\)|\((77,126,119,56)\)|

厳密な三変数 \(b_2\) 評価を別に作る必要はない。表は (W-5G) と (W-F) の代入であり、offsetの有限fixtureではない。□

### W-FIVE-HIGH　\(q=3,u\ge8\) の全高次行

(W-S1–2) の一般資源は \(4W\le u^2\)、\(\widehat R\le W-u\) を与える。
\(u=8\) では同じ有限等差和をそのまま残すと \(W\le8+(8-4)+(8-4-2)=14\)。
W-HIGH の \(B=14\) に対し \(U_2(B)=10B-4u-4=104\le2\binom83=112\) である。
\(u\ge9\) では \(B=u^2/4\) とし、
\[
 2\binom u3-\left(\tfrac52u^2-4u-4\right)
  =\frac{2z^3+33z^2+136z+33}{6}>0,
 \qquad z=u-9\ge0.                                   \tag{W-5H}
\]
が第二行の差である。どちらの場合も \(P\le B,\widehat R\le B-u\) なので、
W-HIGH が同じ第二行比較を全 \(2\le i\le5\) へ移す。
この高次行証明はantipodal構造か否かを問わない。□

### W-FIVE-FIRST　\(q=3,u\ge8\) の第一行

四元集合 \(A=\{0,a,b,c\}\) に対し、Kneserの増分が3未満になるには、
stabilizerの位数 \(f\) と \(A+H\) のcoset数 \(c_0\) が
\((c_0-1)f\le2,c_0f\ge4,c_0\ge2\) を満たす必要がある。
\(f=1\) なら \(c_0\ge4\) で矛盾、\(f\ge3\) でも矛盾するため、\(f=c_0=2\) のみ。
このとき \(A\) は二つの \(H\)-cosetの全体である。
巡回群の位数2の部分群は \(\{0,u/2\}\) なので、元の整数offsetは
\[
 u=2h,\quad A=\{0,t,h,t+h\},\quad0<t<h,\quad\gcd(t,h)=1. \tag{W-APD}
\]
最後のgcd条件は \(A\) の生成性から従う。この配置は群のunit作用や反射でsourceを取り替えたものではない。
この場合はantipodal補題 APD.2 を適用する。同補題は候補語からの \(P\) の上界と調和評価だけで第一行を払い、
厳密presentation、\(P,W,b_1\) の等式を主依存に含まない。

antipodalでない場合は、全群に達する前の増分がすべて3以上なので
\[
 W\le B_3(u):=u+\sum_{j\ge0}(u-4-3j)_+.
\]
(W-S2) の等差和の等式部分は任意の正整数 \(s\) で成立する。
ここで \(a=4,s=3\)、\(u-4=3k+b\)、\(0\le b<3\) とすれば
\[
 6B_3(u)=u^2+u+4+b(3-b)\le u^2+u+6.                  \tag{W-5V}
\]
最後は整数 \(b=0,1,2\) のいずれでも \(b(3-b)\le2\) だからである。
第一行のfourth評価は \(b_1\le P/2+5\) だから、(W-T) により
\[
 \beta_1(G)\le\tfrac52W-u+5
 \le B:=\frac{5u^2-7u+90}{12}.
\]
整数容量を \(A=\binom u2+1\)、\(z=u-8\ge0\) とすると
\[
 A+1-B=\frac{u^2+u-66}{12}
       =\frac{z^2+17z+6}{12}>0.                       \tag{W-5I}
\]
従って \(\beta_1(G)\le B<A+1\)。Betti数の整数性により \(\beta_1(G)\le A\) となり、
全 \(u\ge8\) が一つの不等式で閉じる。\(u=8\) の別扱いも三剰余の容量差も不要である。□

## 4.5　この章の全域合成

\(e\ge6\) では \(u=e-1,e\) を W-AP と W-HOLE、
\(e+1\le u\le2e-3\) を W-DENSE、\(u\ge2e-2\) を W-SPARSE が覆う。
\(e=5\) では \(u=4,5\) を同じ端の二補題、\(u=6,7\) を W-FIVE-SMALL、
\(u\ge8\) を W-FIVE-HIGH と W-FIVE-FIRST が覆う。
従って元のsource、任意体、\(m\ge du+2\)、全 \(d\ge1\)、全正行についてliteral targetとの比較を得る。
第0行とsource消滅後の行を共通接続補題で加えれば、全 \(i\ge0\) が閉じる。□


# 五生成元の antipodal 分岐：候補語だけによる閉鎖

本節の `APD` は幅別の第一行評価に挿入する補題である。端点章の記号を使い、
\(P=P_C=\dim_k Q_C\)、\(R=\dim_k H_2(x,v;G)\)、\(W\) は**同じ向きの元のデータ**の距離和とする。
\(P_G\) と \(P_C\) の同一性は仮定しない。

## APD.1　必要なのは候補語による上界だけである

**補題。** \(h\ge4\)、\(0<t<h\)、\(u=2h\) とする。任意体 \(k\) 上で
\[
C=k[s,sT^t,sT^h,sT^{t+h},sT^{2h}],\qquad Q_C=C/(x,v)C,
\]
\(x=s,v=sT^{2h}\) と置く。内部変数 \(y,z,w\) の像をそれぞれ
\(sT^t,sT^h,sT^{t+h}\) とすると、\(Q_C\) は
\[
 z,\qquad y^{n-j}w^j\quad(0\le j\le n<h)
 \tag{APD.1}
\]
で張られる。特に
\[
 P\le1+\sum_{n=0}^{h-1}(n+1)=\binom{h+1}{2}+1.
 \tag{APD.2}
\]
この上界に \(\gcd(t,h)=1\) は不要である。

**証明。** \(C\) では、両座標「次数・offset」を比較して
\[
 yz=xw,\qquad z^2=xv,\qquad zw=vy
 \tag{APD.3}
\]
が成立する。従って \(Q_C\) の単項式で \(z\) を含むものは、\(z\) 自身を除いて全て0である。

次に \(0\le j\le h\) とし、\(t+j=2K+r\)、\(r\in\{0,1\}\) と書く。
\(t+j\le2h-1\) より \(K\le h-1\)、\(r+K\le h\) である。\(C\) 内で
\[
 y^{h-j}w^j=x^{h-r-K}z^r v^K
 \tag{APD.4}
\]
が成立する。実際、両辺の次数は \(h\)、offset はともに \(h(t+j)\) である。
端点の指数和は \(h-r>0\) なので右辺は \((x,v)C\) に属する。
よって \((y,w)\) の次数 \(h\) の語は全て0であり、それ以上の語も次数 \(h\) の因子を持つので0である。
\(C\) は五つの単項式で生成され、商では \(x,v\) が消えるから、残る像は (APD.1) で尽くされる。
候補語の独立性を主張せずに個数を数えれば (APD.2) を得る。□

## APD.2　第一行の支払い

**補題。** \(e=5\)、\(u=2h\ge8\) の実端点データの内部 offset が
\(\{t,h,t+h\}\)、\(0<t<h\) なら、任意体について
\[
 \beta_1(G)\le\binom u2+1.
 \tag{APD.5}
\]

**証明。** 端点章の実核を補償した Tor 評価、Artin 商の親子調和評価、同じ向きの距離和評価は
\[
 \beta_1(G)\le b_1(Q_C)+P+R,
 \qquad b_1(Q_C)\le\frac23P+\frac{10}{3},
 \qquad R+u\le W.
 \tag{APD.6}
\]
ここで有理数は次元の整数不等式の重みであり、\(k\) の中で3を割らない。
四点剰余集合の一般増分 \(2\) による二次距離和評価から
\[
 W\le\frac{u^2}{4}=h^2,\qquad R\le h^2-2h.
 \tag{APD.7}
\]
を得る。(APD.2)、(APD.6)、(APD.7) を合わせると、全 \(h\ge4\) に対して
\[
 \beta_1(G)\le
 \frac53\frac{h^2+h+2}{2}+\frac{10}{3}+h^2-2h
 =B:=\frac{11h^2-7h+30}{6}.
\]
整数容量を \(A=\binom{2h}{2}+1\) と置く。容量に1を加えてから差を取れば
\[
 A+1-B=\frac{h^2+h-18}{6}
 =\frac{(h-4)^2+9(h-4)+2}{6}>0.
 \tag{APD.8}
\]
従って \(\beta_1(G)\le B<A+1\) であり、\(\beta_1(G)\) が整数なので
\(\beta_1(G)\le A\) を得る。\(h=4\) も同じ不等式に含まれ、第一行に特殊な尾和基点は不要である。□

## APD.3　元の幅分岐への適用

幅章の Kneser による四点集合の分類は、例外の場合に**同じ剰余集合**を
\[
 A=\{0,t,h,t+h\}\subset\mathbb Z/(2h),\qquad0<t<h
\]
と書く。各内部 offset はもともと \(0<a<u\) に入るため、剰余表示の一意性から整数 offset も
\(\{t,h,t+h\}\) である。この段階で群の unit 倍や source の置換は行わない。
分類からは \(\gcd(t,h)=1\) も得られるが、APD.1–2 はそれを追加入力として要求しない。

高次行には幅章で証明する、全五生成元データに共通の評価
\[
 \beta_i(G)\le i\binom u{i+1}\qquad(u\ge8,\ i\ge2)
 \tag{APD.9}
\]
を使う。これは antipodal か否かに依存しない。従って APD.5 と APD.9 がこの例外枝の全正行を覆う。
物理幅 \(V=du\) と literal interval completion への移行、第0行と \(i>5\) の扱いは共通接続補題による。
この経路は \(Q_C\) の厳密な presentation、\(P\)・\(W\) の等式、厳密式 \(b_1(Q_C)=h+4\) を使用しない。


# 四生成元の狭幅：二変数の標準語による閉鎖

本章では
\[
\begin{gathered}
S=\langle m,m+da,m+db,m+du\rangle,\quad 0<a<b<u,\\
\gcd(a,b,u)=\gcd(m,d)=1,\quad d\ge1,\quad m\ge du+2.
\end{gathered}
\tag{N0}
\]
を固定する。したがって \(u\ge3\)、物理幅は \(V=du\ge u\) である。
体 \(k\) は任意とし、\(G\) はこの元の \(S\) の完備半群環の接錐である。
比較先は物理幅 \(V\) の実区間補完であり、その Betti 数を \(F_i(m,V)\) と書く。

## N1　二変数の共通入力

\(C=k[s,st^a,st^b,st^u]\)、対応する変数を \(x,y,z,v\) とし、
\(Q_C=C/(x,v)C\) の生きた内部語 \(y^sz^t\) の指数集合を \(D\) とする。
同じ次数・offset の二内部語は
\(s+t=s'+t',\ as+bt=as'+bt'\) より一致する。
従って \(Q_C\) は二変数単項式 Artin 商であり、\(D\) は有限 downset である。
\[
\begin{gathered}
P=|D|,\quad \sigma=\dim_k(0:_{Q_C}(y,z)),\quad R=\dim_k(0:_G(x,v)),\\
H_x=\max_{(s,t)\in D}\left(s+t-\left\lceil\frac{as+bt}{u}\right\rceil\right).
\end{gathered}
\]
空語の height は0とする。\(\ell_r\) は \(\mathbb Z/u\mathbb Z\) における
ステップ \(a,b\) の最短語長、\(W=1+\sum_r\ell_r\) とする。
共通端点移行と二内部変数の Koszul 計算から
\[
P\le W,\qquad
R\le\min\{W-u,\ u\max(H_x-2,0)\},
\tag{N1a}
\]
\[
(\beta_1,\beta_2,\beta_3,\beta_4)(G)
\le(P+\sigma+1+R,\ 2P+\sigma+3R,\ P+3R,\ R).
\tag{N1b}
\]
ここで \(R\) は元の向きの actual socle である。
\(P\) を \(\dim Q_G\) と同一視せず、共通端点章で証明した実核の長さによる補償を含む式を使う。
二変数商の Betti 列 \((1,\sigma+1,\sigma)\) は、top Koszul homology が socle、
分数体上の Euler 式が \(1-b_1+\sigma=0\) であることから得られる。

## N2　距離和と socle 三角形

\(A=\{0,a,b\}\subset\mathbb Z/u\mathbb Z\) とすると
\[
|nA|\ge\min(u,2n+1),\qquad
W\le1+\lfloor u^2/4\rfloor.
\tag{N2a}
\]
実際、\(n=0\) または \(nA\) が全群なら明らかである。
それ以外で \(H=\operatorname{Stab}(nA)\) とする。
商群で \(n\bar A\) は非周期的であり、\(j\bar A\) の stabilizer は
\(n\bar A\) のそれに含まれる。二集合 Kneser を反復して
\[
|nA|\ge n|A+H|-(n-1)|H|
\]
を得る。\(|H|=1\) なら右辺は \(2n+1\)。\(|H|\ge2\) なら
\(A\not\subset H\) が生成条件から従うので \(|A+H|\ge2|H|\)、
右辺は \((n+1)|H|\ge2n+2\) である。
また \(nA=\{r:\ell_r\le n\}\) より
\[
W=1+\sum_{n\ge0}(u-|nA|)
\le1+\sum_{n\ge0}(u-2n-1)_+
=1+\lfloor u^2/4\rfloor.
\]

有限 downset の極大点を第一座標昇順に
\((\alpha_j,\beta_j)\), \(0\le j<\sigma\) と並べる。
第二座標は厳密減少するので
\(\alpha_j\ge j,\ \beta_j\ge\sigma-1-j\)。従って
\[
\{(s,t):s+t\le\sigma-1\}\subset D,\qquad
\binom{\sigma+1}{2}\le P\le W,\qquad \sigma\le u-1.
\tag{N2b}
\]
最後は \(\binom{u+1}{2}>1+u^2/4\)（\(u\ge3\)）による。
単項式基底では socle は極大点で張られる。異なる基底語の生きた
\(y\) または \(z\) 倍が一致しないため、線形結合の相殺による追加 socle はない。
この三角形の**包含**は後で禁止語との矛盾に使う。

## N3　純語・混合語と元の height

純標準語の長さは \(u-2\) 以下である。
例えば \(g=\gcd(a,u)>1\) なら \(q=u/g\le u-1\) として
\(y^q=x^{q-a/g}v^{a/g}\)。\(g=1\) なら
\(qa\equiv b\pmod u\) となる \(2\le q\le u-1\) があり、
\(qa=b+ku\), \(0\le k\le q-1\) と書けば
\(y^q=x^{q-1-k}zv^k\)。いずれも端点を含むので \(y^q\) は禁止語である。
\(a,b\) を交換した同じ議論が純 \(z\) 語にも適用される。

混合標準語に対応する \(a,b\) の列は零和自由である。
非空零和部分列の長さが \(j\)、整数和が \(Ku\) なら
\(1\le K\le j-1\) であり、その因子を \(x^{j-K}v^K\) に替えると端点表示ができるためである。
長さが \(u/2\) を超えると仮定する。Savchev–Chen の長零和自由列定理により、
ある unit を列の各項に掛けた正代表値の和が \(u-1\) 以下となる。
両代表値が2以上なら和が \(u\) を超えるから、ラベルを必要なら交換して値は \(1,c\), \(c\ge2\)。
元の整数 offset を \(\alpha,\beta\in\{a,b\}\)、個数を \(R_0,T_0\ge1\) とする。
unit を消去すると \(c\alpha\equiv\beta\pmod u\)。従って
\[
c\alpha=\beta+ku,\quad 0\le k\le c-1,\qquad
Y_\alpha^c=x^{c-1-k}Y_\beta v^k.
\tag{N3a}
\]
指数の範囲は \(-u<c\alpha-\beta<cu\) から従う。
右辺は \(c-1>0\) 個の端点を含むので \(R_0<c\) である。
また \(R_0+cT_0\le u-1\) より
\[
2(R_0+T_0)=(R_0+cT_0)+(R_0-(c-2)T_0)
\le(u-1)+(c-1-(c-2))=u,
\]
矛盾する。unit は有限群の列にだけ用い、\(G,R,H_x\) を変換していない。
\(h=\lfloor u/2\rfloor\) とすると
\[
st>0\Longrightarrow s+t\le h,\qquad
s+t\le u-2\ ((s,t)\in D),\qquad H_x\le u-3.
\tag{N3b}
\]
最後は非空語の \(\lceil(as+bt)/u\rceil\ge1\) による。
特に \(u=3,4\) では元の \(R=0\) である。

## N4　全高次行を一つの三次式で払う〔新しい短縮〕

\((N1),(N2)\) より
\[
\beta_2\le U_2=5u^2/4-2u+4,\quad
\beta_3\le U_3=u^2-3u+4,\quad
\beta_4\le U_4=u^2/4-u+1.
\tag{N4a}
\]
例えば第2行は \(2P+\sigma+3R\le5W-2u-1\)、他は
\(P+3R\le4W-3u\)、\(R\le W-u\) である。
\(T_i(u)=i\binom u{i+1}\) と書く。\(u=6+z\), \(z\ge0\) では
\[
12(T_2-U_2)=4z^3+45z^2+140z+36>0.
\tag{N4b}
\]
従って \(T_2\) が第2行を払う。さらに
\[
U_2-U_3=u^2/4+u>0,\quad U_2-5U_4=3u-1>0,
\]
\[
\frac{T_3}{T_2}=\frac{3(u-3)}8\ge1,\qquad
\frac{T_4}{T_2}=\frac{(u-3)(u-4)}{10}\ge\frac15
\qquad(u\ge6).
\tag{N4c}
\]
よって \(\beta_3\le U_3\le U_2\le T_2\le T_3\)、
\(\beta_4\le U_4\le U_2/5\le T_2/5\le T_4\)。
\(F_i(m,V)\ge T_i(V)\ge T_i(u)\) により全 \(u\ge6\) が閉じる。
この除法は正の整数の有理数としての比較であり、係数体内で割っていない。
旧稿の第3・4行用の四次・五次式も、第2行の補正容量 \(+V\) も不要になった。

小幅は次の通りである。

| \(u\) | 用いる入力 | 第2–4行上界 | target最小値 |
|---:|---|---|---|
|5|\(P\le7,R\le2,\sigma\le4\)|\((24,13,2)\)|\((25,25,9)\)|
|4|\(P\le5,\sigma\le2,R=0\)|\((12,5,0)\)|\((12,7,1)\)|
|3|\((P,\sigma,R)=(3,2,0)\)|\((8,3,0)\)|本文参照|

\(u=5\) の \(P\le7\) は \((N2a)\) の床を保持した値であり、
\(u=4\) の \(\sigma\le2\) は \((N2b)\) から従う。
\(u=3\) では \(y^2=xz,yz=xv,z^2=yv\) により \(Q_C=k[y,z]/(y,z)^2\) となる。
この幅で \(d=1\) なら source=target、\(d\ge2\) なら \(V\ge6\) の容量が払う。
表の target 値は共通容量式の剰余最小値を代入したものなので、
\(V\ge u\) と各行の容量の非減少性が全 \(d,m\) への支払いを与える。

## N5　三関係の計数で第一行を一括処理する

core 内に
\[
y^b=x^{b-a}z^a,\qquad
z^{u-a}=y^{u-b}v^{b-a},\qquad
y^{u-b}z^a=x^{u-b}v^a
\tag{N5a}
\]
がある。従って左辺とその倍数は \(D\) に属さない。
\(k_0=u-b+a\in[2,u-1]\)、\(h=\lfloor u/2\rfloor\) と置き、
\[
E_h(k_0)=
\begin{cases}\binom{h-k_0+2}{2},&k_0\le h,\\0,&k_0>h\end{cases}
\]
と定める。二軸は \(1+(b-1)+(u-a-1)=2u-k_0-1\) 点以下。
混合語は \(s,t\ge1,s+t\le h\) の \(\binom h2\) 点内にある。
第三関係の倍数を \((s,t)=(u-b+i,a+j)\) と書くと
\(i,j\ge0,i+j\le h-k_0\) であるから、その三角形内から正確に \(E_h(k_0)\) 点を除ける。
\[
P\le2u-k_0-1+\binom h2-E_h(k_0)
\le2u-h-2+\binom h2.
\tag{N5b}
\]
後半は、\(k_0\le h\) で \(j=h-k_0\) とすれば
\(k_0+E_h(k_0)=h+1+j(j+1)/2\ge h+1\)、
\(k_0\ge h+1\) でも同じ下界が成立することによる。

混合 socle の第一指数は相異なる \(1,\ldots,h-1\) であり、二軸から高々2点を加えて
\(\sigma\le h+1\)。また \(\sigma\ge k_0+1\) なら \((N2b)\) の三角形包含により
禁止語 \(y^{u-b}z^a\) が標準となる。従って
\[
\sigma\le\min(h+1,k_0).
\tag{N5c}
\]
\((N1),(N2),(N5b,c)\) を合わせると
\[
\beta_1(G)\le \binom h2+u+1+\lfloor u^2/4\rfloor.
\]
\(L_1(u)=\binom u2+1\) から右辺を引いた差は
\[
\frac{h(h-5)}2\quad(u=2h),\qquad
\frac{h^2-3h-2}2\quad(u=2h+1).
\tag{N5d}
\]
偶数 \(u\ge10\)、奇数 \(u\ge9\) では非負。
また \(u=5\) は \(P\le7,\sigma\le3,H_x\le2\) から
\(R=0,\ \beta_1\le11=L_1(5)\)。
\(F_1(m,V)\ge L_1(V)\ge L_1(u)\) によりこれら全域が閉じる。

## N6　幅6–8と幅3・4の残る第一行

以下も \(H_x,R\) は元の向きで評価する。
一方向の指数が \(c-1\) 以下の downset の極大点は第一座標が相異なるため高々 \(c\) 個である。

**\(u=6\)。** \(P\le10,\sigma\le4,H_x\le3\)。\(H_x\le2\) なら第一行は高々15。
\(H_x=3\) を与える語は次数4で切上げ offset 商が1でなければならない。
混合次数4は \((N3b)\) に反し、純 \(z^4\) は \(4b\ge8\) なので不可能。
純 \(y^4\) なら \(4a\le6\) より \(a=1\)、
\(y^b=x^{b-1}z\) により \(b\le4\) も不可能なので \(b=5\)。
この場合 \(yz=xv,y^5=x^4z,z^5=yv^4\) から
\(P\le9,\sigma\le2\)、\(R\le W-6\le4\) で第一行は高々16。
両場合とも \(L_1(6)=16\) が払う。

**\(u=7\)。** \(h=3,R\le6\) より第一行上界は
\(23-k_0-E_3(k_0)+\min(4,k_0)\)。
\(k_0=2,3\) で20,22、\(k_0\ge5\) で \(27-k_0\le22=L_1(7)\)。
残る \(k_0=4\) は次の三対である。

|\((a,b)\)|追加関係|\((P,\sigma)\) 上界|第一行上界|
|---|---|---|---:|
|(1,4)|\(y^4=x^3z,\ z^2=yv\)|\((7,2)\)|16|
|(2,5)|\(yz=xv\) と \((N5a)\)|\((9,2)\)|18|
|(3,6)|\(y^2=xz,\ z^4=yv^3\)|\((7,2)\)|16|

外側二対は二軸が高々5点、混合語は次数3以下かつ一方の指数が1なので高々2点。
socle は幅2の strip により高々2点。中央は混合語がなく、二軸だけで上界を得る。

**\(u=8\)。** \(h=4,R\le9\) より第一行上界は
\(31-k_0-E_4(k_0)+\min(5,k_0)\)。
\(k_0=2,3\) で25,28、\(k_0\ge7\) で \(36-k_0\le29=L_1(8)\)。
\(k_0=4,5,6\) だけを次のように処理する。

|\(k_0\)|gcd 条件を満たす対|追加関係・包含|\((P,\sigma)\) 上界|第一行上界|
|---:|---|---|---|---:|
|4|(1,5),(3,7)|順に \(y^5=x^4z,z^5=xyv^3\)、\(y^5=x^3zv,z^5=yv^4\)|\((14,4)\)|28|
|5|(1,4),(2,5),(3,6),(4,7)|順に \(z^2=xv,z^2=yv,y^2=xz,y^2=xv\)|\((9,2)\)|21|
|6|(1,3),(5,7)|\((N5a)\) による幅3の strip|\((14,3)\)|27|
|6|(3,5)|\(yz=xv\)|\((9,2)\)|21|

\(k_0=4\) では二軸は9点以下、次数4以下の混合三角形6点から
\((N5a)\) が \((3,1)\) または \((1,3)\) を除くので \(P\le14\)。
\(\sigma\le k_0=4\) を使う。
\(k_0=5\) は一方の純冪指数2、他方5以下なので二軸6点以下、混合3点以下、socle は2点以下。
\(k_0=6\) の外側二対は純冪指数が一方3、他方7以下。
二軸9点以下、混合語は高々 \(3+2=5\) 点、socle は3点以下。
中央は混合語がない。対の網羅性は \(b-a=8-k_0\) を解き、
\(k_0=4,6\) では偶数の対を \(\gcd(a,b,8)=1\) により除くことで得られる。
したがって有限表は exact core 値の計算証書ではなく、表示関係と包含の証明の整理である。

**\(u=3,4\)。** \(u=3\) は \((1,2)\) のみ。
\(d=1\) なら source=target、\(d\ge2\) なら上界6を \(V\ge6\) の容量16以上が払う。
\(u=4\) は \(P\le5,\sigma\le2,R=0\) より上界8。
\(d\ge2\) は \(V\ge8\) の容量29以上が払う。
\(d=1\) の \((a,b)=(1,2),(2,3)\) は \(y^2,z^2\) が端点表示を持つため
\(D\subset\{1,y,z,yz\}\)。\(P=4\) なら \(\sigma=1\)、\(P\le3\) なら \(\sigma\le2\) なので
\(P+\sigma\le5\)、第一行は高々6。
残る \(d=1,u=4,(a,b)=(1,3)\) を次に処理する。

## N7　幅4の最後の族：全ての長い競合を調べる

ここだけ \(d=1,u=4,(a,b)=(1,3),m\ge6\) とする。
\(k[x,y,z,v]\to C=k[s,st,st^3,st^4]\) の核に
\[
y^3-x^2z,\quad yz-xv,\quad xz^2-y^2v,\quad z^3-yv^2
\tag{N7a}
\]
がある。内部重み \((\mathrm{wt}(x),\mathrm{wt}(y),\mathrm{wt}(z),\mathrm{wt}(v))=(0,1,2,0)\)、
通常次数、固定 lex の順の大域的単項式順序を取る。
左辺の重みは \(3,3,4,6\)、右辺は \(2,0,2,1\) なので候補先頭 ideal は
\(J_0=(y^3,yz,xz^2,z^3)\)。標準語は自由列
\(x^Lv^Kb\), \(b\in\{1,y,y^2,z\}\), \(L,K\ge0\) と、制限列 \(z^2v^K\) である。
自由列の offset 剰余は \(0,1,2,3\) と相異なる。
制限列の offset は \(6+4K\)、次数は \(2+K\)。
同じ offset の自由列は \(x^Ly^2v^{K+1}\) だけで次数は \(L+K+3>2+K\)。
各列内の次数・offset も \(L,K\) を一意に定める。
従って余りの像は \(C\) で独立であり、停止する除算により \((N7a)\) は core の完全 Gröbner 基底となる。

基点 \(b\) の次数・offset を \((c,n)\) とする。
短い標準語 \(x^Lv^Kb\) の実指数は \((L+K+c)m+n+4K\)。
これが actual 接錐で消える条件は、同じ実指数に次数が \(j\ge1\) 大きい表示が存在することである。
その表示を core の標準列へ直す。自由 anchor の剰余と座標を
\[
\begin{gathered}
r_j=(n-jm)\bmod4,\quad
\kappa_j=(jm+r_j-n)/4=\left\lceil\frac{jm-n}{4}\right\rceil,\\
(\lambda(0),\lambda(1),\lambda(2),\lambda(3))=(0,1,2,1).
\end{gathered}
\]
と書く。offset と次数の等式をそれぞれ解くと
\[
K'=K-\kappa_j,\qquad
L'=L+c+j+\kappa_j-\lambda(r_j)=L-\Delta_j,
\quad \Delta_j=\lambda(r_j)-c-\kappa_j-j.
\tag{N7b}
\]
従って自由 anchor の競合条件は正確に \(K\ge\kappa_j,L\ge\Delta_j\)。
全基点で \(4c-n\ge0\)、全剰余で \(4\lambda(r)-r\le6\) だから
\[
4\Delta_j=(4\lambda(r_j)-r_j)-(4c-n)-j(m+4)
\le6-(m+4)<0.
\tag{N7c}
\]
従って第二条件は自動的である。
剰余2の制限 anchor \(z^2\) による競合では \(K' =K-\kappa_j-1\) なので
\(K\ge\kappa_j+1\) が必要となり、同じ \(j\) の自由 anchor の条件に含まれる。
標準列は全て尽くされ、\(\kappa_j\) は \(j\ge1\) で非減少なので、
全ての長い競合を調べた正確な消滅条件は \(j=1\) の閾値
\[
\theta_n=\max\left(\left\lceil\frac{m-n}{4}\right\rceil,0\right),
\quad
J=J_0+(bv^{\theta_n}:b=1,y,y^2,z,z^2)
\tag{N7d}
\]
である。差 \(m-n\) と切上げは整数で取り、その後に0との最大を取る。

禁止語は長い表示を持つので actual 接錐で0。
非禁止語は最大分解長が元の次数に等しく、同次数の異なる core 標準語は
offset、従って実指数が相異なるので、その actual 像は独立である。
まず \((N7a)\) で除算し、禁止語を除くと核の非禁止余りは0であることから
\(\operatorname{in}(I_G)=J\) を得る。
\(J\) の各極小生成元を先頭項に持つ \(I_G\) の同次式を選べば、
それらの停止除算で余りは0となるので \(I_G\) を生成する。
従って任意体で \(\beta_1(G)=\mu(I_G)\le\mu(J)\)。

\(m=6\) は \(J=(v^2,zv,z^2,yz,y^2v,y^3)\)、\(\mu(J)=6<9=F_1(6,4)\)。
\(m>6\) では全ての \(\theta_n\) が正であり、\(xz^2\) は常に極小生成元。
残りの常在する極小生成元は \(y^3,yz,z^3,v^{\theta_0}\)。
四候補 \(yv^{\theta_1},y^2v^{\theta_2},zv^{\theta_3},z^2v^{\theta_6}\) の極小性条件は
順に \(\theta_1<\theta_0,\theta_2<\theta_1,\theta_3<\theta_0,\theta_6<\theta_3\) である。
\(m=4Q+\rho\), \(0\le\rho<4\) を代入すると全 \(Q\) で次を得る。

\[
\begin{array}{c|ccccc|cc}
\rho&\theta_0&\theta_1&\theta_2&\theta_3&\theta_6&\mu(J)&F_1(m,4)\\\hline
0&Q&Q&Q&Q&Q-1&6&7\\
1&Q+1&Q&Q&Q&Q-1&8&10\\
2&Q+1&Q+1&Q&Q&Q-1&8&9\\
3&Q+1&Q+1&Q+1&Q&Q&6&8
\end{array}
\]

これで最後の族も全 \(m\ge6\) で閉じる。係数は二項式の \(\pm1\) だけであり、
独立性は実半群基底によるため任意標数で有効である。

## N8　四生成元の coverage

第一行は \(u=3,4\) を N6–N7、\(u=5\) と \(u\ge9\) を N5、
\(u=6,7,8\) を N6 が覆う。第2–4行は N4 が全幅を覆う。
第0行は両辺1、第4行を超える source の行は Hilbert syzygy により0。
従って \((N0)\) の全パラメータ、全 Betti 行について
\(\beta_i(G_S;k)\le\beta_i(G_{\widetilde S};k)\) が成立する。
196組の core 証書は本章の入力ではなく、各 \(m,d\) の有限上限も設けていない。


# 6 全域と全行の合成

## 6.1 小生成元

\(e=1\) なら数値半群のgcd条件により唯一の原子は1である。
従って \(S=\mathbb N=\widetilde S\)、接錐は \(k[X]\) で、Betti列は
\((1,0,0,\ldots)\)。この場合はoffsetの空集合にgcdを定義する必要がない。

\(e=2\) なら \(S=\langle m,n\rangle\)、\(m<n\)、\(\gcd(m,n)=1\) であり、
完備半群環の最小表示は \(k[[X,Y]]/(Y^m-X^n)\)。この主イデアルの任意の非零元の
最低次数形は、その係数の最低次数形と \(Y^m\) の積であるから、接錐は
\(k[X,Y]/(Y^m)\) である。Betti列は \((1,1,0,\ldots)\)。
targetは \(v\ge1\) のintervalであり、(CAP) の第一行は
\(\binom v2+D\ge1\)。他の正行のsourceは0なので比較が従う。

\(e=3\) は公刊入力LTVを用いる。同定される比較先はliteral interval completionであり、
各環自身の最小表示を使う。定義イデアルの第 \(j\) Betti数は商の第 \(j+1\) Betti数に
等しいので、正行全ての比較が得られる。第0行は両側1である。

## 6.2 パラメータの被覆

以下 \(e\ge4\)。整数幅 \(w=g_e-m\) は \(w\ge m-1\) 又は \(w\le m-2\) の
どちらかであり、間の整数はない。前者では (ORDCAP) がtargetであり、第2章が比較を閉じる。
cut本数 \(2\le r\le e-1\) は \(r=2,3\)、\(4\le r\le8\)、\(r\ge9\) に分かれ、
最後の場合は \(e\ge r+1\ge10\)。\(r\ge3\) ではcutの構成から
\(\delta\ge\binom{r+1}2\) が従う。\(\delta=0\) は \(r=2\) の空の塔として扱う。

後者では BRIDGE により同じ元の \(S\) の端点データを作り、物理幅 \(du=w\) と
\(m\ge du+2\) を保つ。\(e=4\) には第5章、\(e\ge5\) には第4章を適用する。
全ての枝は次の表で尽くされる。

| sourceの範囲 | 分割 | 比較を閉じる証明 |
|---|---|---|
| \(e\le3\) | \(e=1,2,3\) | §6.1 |
| \(e\ge4,w\ge m-1\) | \(r=2,3;\ 4\le r\le8;\ r\ge9\) | ordinary章 |
| \(e\ge6,w\le m-2\) | \(u=e-1,e;\ e+1\le u\le2e-3;\ u\ge2e-2\) | W-AP、W-HOLE、W-DENSE、W-SPARSE |
| \(e=5,w\le m-2\) | \(u=4,5;\ u=6,7;\ u\ge8\) | 端の二幅、小幅、全高次行と第一行分類 |
| \(e=4,w\le m-2\) | \(u=3,4;\ u=5;\ u=6,7,8;\ u\ge9\) | N4章。幅4の最後の族は全 \(m\) の競合証明 |

## 6.3 主定理の結論

前節の各枝で \(1\le i\le e\) の比較が得られた。
特に上端 \(i=e\) はsourceの消滅行として捨てず、ordinaryの末端Tor又は端点の
\(\beta_{q+2}\le R\) を含めて処理した。N4の \(i=4\) も同じである。
最小幅の \(d=1\) で最小容量だけでは支払えない枝には、同じsourceとtargetの一致又は
actual剰余容量を使った。境界 \(m=du+2\) は全端点データの仮定に含まれている。

BRIDGE により代数的接錐から元の完備接錐へ戻せる。ordinaryで一般cutのために体を
拡大した場合も、同標数flat base changeによるBetti一致で元の \(k\) へ戻す。
両側第0行は1、\(i>e\) はsourceが0である。これで元の \(S\)、任意体 \(k\)、
各環自身の最小表示、literal interval completionについて全 \(i\ge0\) の (MAIN) が従う。\(\square\)

