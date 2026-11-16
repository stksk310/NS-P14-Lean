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
