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
