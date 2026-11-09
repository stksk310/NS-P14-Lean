# 小ordinaryの83組を不要にする追加簡約

2026年11月9日。監査中のV02本文・証書は変更せず、置換補題だけを記す。
これは第2–10節の共通基礎を前提とする追加証明であり、Lean形式検証ではない。

**結論：小ordinaryの83組・665行比較と5本の無限tailは、下記の5行の有理数表で置換できる。**
第15節のfirst-hit・truncated lex・tailの議論を、主定理の依存から丸ごと外せる。
前回のN4置換と併用すると、V02第17節が必須としていた二種類の大きな列挙証書は
いずれも不要になる。少数の有理比較、代数的場合分け、公刊定理への依存は残る。

## 1 二次層が最大ならmultiplicityは大きい

V02第2節のactual Apéry商 \(Q\) と \(q_2=\dim_k Q_2\) を用いる。
真正な最小生成系を \(\Gamma=\langle m=g_1<g_2<\cdots<g_e\rangle\) とする。
次を示す。

\[
q_2=\binom e2
\quad\Longrightarrow\quad
m\ge e(e-1)+1,\qquad \delta=m-e\ge(e-1)^2.
\tag{SO1}
\]

非\(m\)生成元に対応する \(e-1\) 変数の二次単項式は \(\binom e2\) 個であり、
それらから \(Q_2\) への写像は全射である。次元が等しいので、この写像は同型である。
従ってすべての二次単項式が、相異なる次数2の非零Apéry座標を与える。

\[
B=\{0,\overline{g_2},\ldots,\overline{g_e}\}
\subset\mathbb Z/m\mathbb Z
\]

と置く。各 \(g_i\ (i>1)\) はApéry元である。そうでなければ \(g_i-m\in\Gamma\)
によりatomでなくなる。また、相異なるApéry元は相異なる剰余を持つ。
従って \(|B|=e\) である。

\(B\) の二項和を、順序を無視し、同じ項の反復を許して考える。
二次単項式同士の和は相異なる剰余を持つ。それらは0やatomの剰余とも一致しない。
各剰余のApéry元は一意であり、0・atom・これらの二次積の次数はそれぞれ0・1・2だからである。
従って、これらの二項和はすべて相異なる。

ここで \(b\ne c,\ b'\ne c'\) に対して \(b-c=b'-c'\) とすると
\(b+c'=b'+c\) である。二項和の一意性より
\(\{b,c'\}=\{b',c\}\) となる。これは同じ順序対を与えるか、除外した \(b=c\) を与える。
従って \(e(e-1)\) 個の非対角の順序対の差は、群の非零元へ単射になる。
群の非零元は \(m-1\) 個なので (SO1) を得る。□

この議論は標数によらない。使用したのは実際のApéry座標と有限集合の単射である。

第4節のcutで \(r=e-1\) かつ \(r\ge3\) なら
\(q_2\ge a_r:=\binom{r+1}{2}=\binom e2\) なので、実際には等号となり (SO1) が適用できる。
\(r\ge3\) では \(r^2>a_r\) だから、

\[
e=r+1,\qquad \delta=a_r
\tag{SO2}
\]

という角は \(r\ge3\) のactual sourceでは起こらない。
\(r=2\) は \(\max(2,p(q_2))\) の特例であり、この含意には含めない。
以下で必要なのは \(r=6,7,8\) の3個だけである。

## 2 同じ資源列を、別の固定cutoffで評価する

\(r\ge4,\ a=a_r,\ e\ge r+1,\ \delta\ge a\) とする。
V02第5・10節の同じ資源列について

\[
\begin{gathered}
M=e+\delta-1,\qquad \mathcal V=e+\delta/2-3/2,\\
H_0=\delta,\quad H_t\ge0,\quad
\sum_{t\ge0}H_t\le\delta\mathcal V,\quad H_t\le M,\quad H_1\le M-a,\\
F_r=(r-1)\delta+\frac{r+1}{2}H_1+
\sum_{t\ge2}\frac{r-1}{t+1}H_t
\end{gathered}
\]

が成り立つ。\(\delta\) はmultiplicity deficitであり、狭幅側のdilation \(d\) とは別の量である。

整数 \(n\ge r\) を固定し、
\(\alpha=(r-1)/(n+1),\ c=(r+1)/2-\alpha,\ \mathcal H_n=\sum_{j=1}^n1/j\)
と置く。第11節(S4)と同じく各重みから \(\alpha\) を引くと

\[
\begin{aligned}
F_r\le U(e,\delta):={}&
\alpha\delta\mathcal V+(r-1-\alpha)\delta+c(M-a)\\
&+M\sum_{j=2}^{n-1}\left(\frac{r-1}{j+1}-\alpha\right).
\end{aligned}
\tag{SO3}
\]

実際、最後の係数は \(j<n\) で正、\(j=n\) で0、\(j>n\) で負である。
従って資源列の台を有限に制限してはいない。

\(G(e,\delta)=\delta(\mathcal V+1)-U(e,\delta)\) とし、
\(e=r+1+s,\ \delta=a+t,\ s,t\in\mathbb Z_{\ge0}\) と書く。
次の定数を置く。

\[
\begin{gathered}
g=G(r+1,a),\\
A=a-1-(r-1)\left(\mathcal H_n-2+\frac{a+2}{n+1}\right),\\
b=G(r+1,a+1)-G(r+1,a)=A+2-\alpha(r-1).
\end{gathered}
\]

すると厳密な恒等式

\[
\boxed{
G(r+1+s,a+t)
=g+sA+tb+(1-\alpha)\left(\binom t2+st\right)}
\tag{SO4}
\]

が成り立つ。途中式として、(SO3)から \(G\) の \(e\) の係数は
\[
A(\delta)=\delta-1-(r-1)\left(\mathcal H_n-2+\frac{\delta+2}{n+1}\right)
\]
であり、\(A(a+t)=A+(1-\alpha)t\) となる。また
\[
G(r+1,a+t+1)-G(r+1,a+t)=b+(1-\alpha)t.
\]
後式を \(t\) 回足し、さらに \(sA(a+t)\) を加えると (SO4) を得る。
従って無限範囲の根拠はこの恒等式であり、有限点での試算ではない。

## 3 五つの有理数行で全域を閉じる

各行で、最後の三列は共通の正の分母 \(L\) を持つ。

| \(r\) | \(a\) | \(n\) | \(L\) | \(Lg\) | \(LA\) | \(Lb\) |
|---:|---:|---:|---:|---:|---:|---:|
|4|10|7|280|2443|762|1007|
|5|15|10|6930|39380|28429|32209|
|6|21|13|72072|−7479|424147|439591|
|7|28|17|2042040|−12196485|17076937|17076937|
|8|36|21|739024|−5070732|8418651|8250691|

全行で \(A,b>0\)、また \(1-\alpha>0\) である。

- \(r=4,5\) では \(g>0\) なので、(SO4)はすべての \(s,t\ge0\) で正。
- \(r=6,7,8\) では \(g+A>0,\ g+b>0\)。従って \(s\ge1\) または \(t\ge1\) なら正。
  残る \(s=t=0\) は (SO2) によりactual sourceでは起こらない。

これで、すべてのactual sourceの \(4\le r\le8\) に対して
\[
F_r<\delta(\mathcal V+1)
\tag{SO5}
\]
を得る。

## 4 全ordinaryへの接続と置換範囲

ordinary側で \(r=2,3\) は既存の第9節を使う。
\(4\le r\le8\) は (SO5) で処理する。
\(r\ge9\) なら \(e\ge r+1\ge10\) なので、既存の第11節を使う。
第8・10節がscalar不等式を全Betti行へ移す。
従って第15節の独立ルートは不要となる。

後の統合では、第11節へ本補題を追加し、第15節を主定理の依存から外し、
第16節のordinary分岐と第17節の必須証書一覧を更新すればよい。
第11節にある \(r=4,\ldots,8\) の旧anchorは新しい表と役割が重なるので、
旧scalar証明を \(r\ge9\) に限定すればその5行も除ける。
今回は監査中の本文を変更していない。

定数の再計算と(SO4)の全係数は
[独立した有理数検算コード](ordinary/verify_ordinary_reduction.py) が確認する。
これは既存の83組証書・既存checkerを読み込まない。
[英語の詳細稿](ORDINARY_REDUCTION.md)、
[Apéry補題の独立点検](SIDON_INDEPENDENT_AUDIT.md)、
[全接続の独立点検](ORDINARY_REDUCTION_REFEREE.md)も保存する。
