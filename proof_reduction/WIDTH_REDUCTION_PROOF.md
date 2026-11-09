# 幅側を有限core計算なしで証明する

## 定理とtarget

\(\Gamma=\langle m,m+da_1,\ldots,m+da_q,m+du\rangle\)、\(e=q+2\ge5\)、\(0<a_1<\cdots<a_q<u<m\)、\(\gcd(m,d)=\gcd(u,a_1,\ldots,a_q)=1\) とする。任意体・全行で、実際のcompletion \(\langle m,m+1,\ldots,m+du\rangle\) へのP14が成立する。

実効target幅は \(V_{\rm tar}=\min(du,m-1)\ge u\)。算術列のBetti公式から、正の第 \(i\) 行は
\[
 F_i^{\min}(u)=i\binom u{i+1}+\min\{\binom u{i-1},\binom ui\}
 \tag{W1}
\]
以上である。範囲外の二項係数は0。算術列半群環の公式と、その場合の接錐とのBetti一致だけをここで使用する。

## 1 実sourceへの移行

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
この平面corner導出の完全な座標記述は、入力の `sources/R39/R39_ACTUAL_SOURCE_CORE_TRANSFER.md` §§2–4 にある。変数数に依存しない原証明だけを使用し、その後の有限core campaignは使用しない。

## 2 密な幅

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
最後の二項は、互いに素な二ブロックに固定点を加える二つの包含単射によって \(\binom{q+2}i\) と \(\binom{q+2}{i-1}\) の双方以下となり、(W1)で払える。端欠落も一つの置換フォームの同じ単位小行列で閉じる。全パラメータの単射と行の端点は、入力 `sources/R40/R40_UNIVERSAL_ONE_GAP.md` §§3–5 の原証明通りであり、有限の行列証明書を仮定しない。

## 3 疎な幅の短いtail

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

## 4 6・7生成元も同じ仕組みで閉じる

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

## 5 5生成元の最後の小幅を列挙せず処理する

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
