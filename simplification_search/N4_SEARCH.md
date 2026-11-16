# N4 の短縮探索：端点評価で枝と有限計算を統合できる

2026-11-09。探索結果であり、現行証明稿は変更していない。

**実質的な短縮が見つかった。** 現行 §12.2 F6 の
\(P_C\le W,\ R\le W-u\) に、三元巡回集合についての Kneser 評価を
一つ加えると、primitive 高次行の 4,824 点・108 tail を全て紙上証明へ
置換できる。第一行も同じ端点評価で処理でき、五支持の計数を使わず、
13,921 offset 組を **196 offset 組**へ縮小できる。
さらに全評価は正規化幅 \(u\) と \(d\ge1\) に共通なので、現行の
nonprimitive/primitive 二枝を統合できる。

Savchev–Chen は第一行の標準語数評価に残る。有限計算を完全に無くした、
あるいは N4 が形式検証済みになった、という主張ではない。

## 1. 置換する範囲と保存する入力

現行本文は `proof_complete/NS_P14_COMPLETE_PROOF_JA.md`。

保存するもの：

- §12.1 の actual interval target 公式と任意体という資格。
- §12.2 の actual endpoint 模型、F6 の socle 評価、F8 の kernel 補償付き
  Koszul 評価。
- NP3/H3 の初等的な「endpoint 最小内部語長は \(u-2\) 以下」の証明。
- P5 の Savchev–Chen による混合標準語長 \(\lfloor u/2\rfloor\) 以下の証明。
- \(d=1,u=4,(a,b)=(1,3)\) についてだけ、B2–B4 の明示 Gröbner 計算と
  実 target の剰余別比較。幅5以上の boundary 議論は不要。

独立な証明成分として不要になるもの：

- §12.3 の nonprimitive 専用の上界・容量多項式の一式。
- §12.4 H7–H9 の全 multiplicity 有限化・actual order 計算・108 tail。
- §12.5 P3 の二面初期 ideal、pure caps の細かな準備、P6–P9 の五支持と \(U\)。
- §12.6 の幅5および幅6以上の boundary family の証明。

共通基礎の説明そのものも重複整理できるが、以下の削減は単なる文章削除ではない。
弱い端点評価が新しい距離和上界により target を支払う、という数学的な置換である。

## 2. 全 d に共通する設定と、既証明の端点不等式

\[
\Gamma=\langle m,m+da,m+db,m+du\rangle,
\quad 0<a<b<u,\quad \gcd(a,b,u)=\gcd(m,d)=1,
\quad d\ge1,\quad m\ge du+2.
\]

\(V=du\) が物理幅。\(C=k[s,st^a,st^b,st^u]\)、
\(Q_C=C/(x,v)C\)、\(P_C=\dim Q_C\)、
\(\sigma_C=\dim(0:_{Q_C}(y,z))\) とする。
\(D\subset\mathbb N^2\) は \(Q_C\) の内部標準語 \(y^sz^t\) の集合。
内部二語の同次数・同 offset は指数まで一致するため、\(Q_C\) は二変数の
単項式 Artin 商である。初期 ideal の二面支持はこの事実に不要。

\(\ell_r\) は mod \(u\) におけるステップ \(a,b\) の最短語長、
\(\ell_0=0\)、\(W=1+\sum_r\ell_r\) とする。
\(R=\dim(0:_G(x,v))\) は actual tangent cone の共通端点 socle である。
F6・F8 により

\[
P_C\le W,\qquad R\le W-u,
\tag{1}
\]
\[
\begin{aligned}
\beta_1(G)&\le P_C+\sigma_C+1+R,\\
\beta_2(G)&\le2P_C+\sigma_C+3R,\\
\beta_3(G)&\le P_C+3R,\\
\beta_4(G)&\le R.
\end{aligned}
\tag{2}
\]

これらは全 \(d\ge1\) に対する評価であり、Cohen–Macaulay 性や
\(\gcd(m,u)=1\) を仮定しない。F3 の競合長増分は \(jd\) である。

(1) の要点も短く再掲する。剰余列の最短点 \((L_r,K_r)\) は
\(L_r+K_r=\ell_r-\boldsymbol1_{r>0}\)。二変数 ideal \(M_r\) の極小点は
この点の左右で高々 \(L_r+K_r+1\) 個なので、総数は \(W\) 以下。
競合 ideal \(T_s\) の極小点数を \(z_s+1\)、最小 v 指数を \(\kappa_s\)
とすると、純 v 冪が存在するので任意の \((p,q)\in T_s\) に対し
\(z_s\le p+q-\kappa_s\)。各最短点の \(j=1\) 競合を使えば
第一座標は \(L_r\) 以下、第二座標は \(K_r+c_r\)。
剰余の置換で \(\sum c_r=m\)、また
\(\kappa_s\ge\lceil(m-s)/u\rceil\)、その右辺の総和は \(m\)。従って
\(\sum z_s\le\sum(L_r+K_r)=W-u\)。
actual 列 \(M_s/(M_s\cap T_s)\hookrightarrow k[x,v]/T_s\) の socle を取れば
\(R\le\sum z_s\) となる。

## 3. 追加する一つの補題：W は u²/4 以下

\(A=\{0,a,b\}\subset\mathbb Z/u\mathbb Z\) とする。全ての \(n\ge0\) について

\[
|nA|\ge\min(u,2n+1).
\tag{3}
\]

証明。\(n=0\) は明らか。\(n\ge1\) で \(nA\) が全群でないとし、
その stabilizer を \(H\) とする。反復 Kneser により

\[
|nA|\ge n|A+H|-(n-1)|H|.
\]

\(|H|=1\) なら右辺は \(2n+1\)。\(|H|\ge2\) なら、
\(A\subset H\) は \(\gcd(a,b,u)=1\) に反するので \(A+H\) は少なくとも
二つの H-coset を含む。右辺は \((n+1)|H|\ge2n+2\)。これで (3)。

0 を padding に使えるため、\(nA\) は正確に \(\ell_r\le n\) の剰余集合。
従って有限和の恒等式と (3) から

\[
\boxed{W=1+\sum_{n\ge0}(u-|nA|)
\le1+\sum_{n\ge0}\max(u-2n-1,0)
=1+\lfloor u^2/4\rfloor.}
\tag{4}
\]

ここは全称証明であり、小幅出力からの外挿ではない。Kneser は既に現行稿の
外部入力に含まれるため、新しい種類の公刊入力を増やさない。

## 4. 高次行：有限点も tail も不要

初等短語補題から \(\sigma_C\le u-1\)。よって (1)(2)(4) より

\[
\begin{aligned}
\beta_2&\le5W-2u-1\le5u^2/4-2u+4,\\
\beta_3&\le4W-3u\le u^2-3u+4,\\
\beta_4&\le W-u\le u^2/4-u+1.
\end{aligned}
\tag{5}
\]

actual interval の既存公式から、\(V\ge3\) で
\(F_2(m,V)\ge2\binom V3+V\)、\(V\ge5\) で
\(F_3(m,V)\ge3\binom V4+\binom V2\)、
常に \(F_4(m,V)\ge4\binom V5\)。これらは V に関し非減少なので、
\(V=du\ge u\) の代わりに u で下から評価すればよい。

第二行、\(u=6+z\)、\(z\ge0\) では

\[
12\{2\binom u3+u-(5u^2/4-2u+4)\}
=4z^3+45z^2+152z+108>0.
\]

\(u=5\) では floor を保ち \(W\le7\)、\(R\le2\)、
\(\sigma_C\le4\) なので \(\beta_2\le24<25\le F_2\)。

第三・四行、\(u=5+z\)、\(z\ge0\) では

\[
8\{3\binom u4+\binom u2-(u^2-3u+4)\}
=z^4+14z^3+67z^2+134z+88>0,
\]
\[
60\{4\binom u5-(u^2/4-u+1)\}
=2z^5+30z^4+170z^3+435z^2+458z+105>0.
\]

\(u=4\) は短語補題から全極小座標の \(L\le1\)。F4 の競合閾値評価により
\(R=0\)。また \(P_C\le W\le5\)。二変数 downset で socle が s 個なら
\(P_C\ge\binom{s+1}2\)（証明は次節）なので \(\sigma_C\le2\)。
従って \(\beta_2\le12\)、\(\beta_3\le5\)、\(\beta_4=0\)。
\(V=4\) の target 最小値は第2行12・第3行7なので成立し、\(V\ge5\) は
上の単調な下界でさらに余裕がある。

\(u=3\) は内部対 (1,2) のみ。\(d=1\) は source=target。
\(d\ge2\) は \(V\ge6\)、\(P_C=3,\sigma_C=2,R=0\) なので
\(\beta_2\le8,\beta_3\le3,\beta_4=0\) を target が支払う。

以上で、全 d の全高次行が紙上で閉じる。

## 5. 第一行：幅13以上を紙上で閉じる

\(h=\lfloor u/2\rfloor\) とする。既存 P5 の Savchev–Chen 論証は
初期 ideal の二面支持に依存しない。endpoint 表示を持たない内部語に
直接適用でき、混合標準語は \(s,t>0,s+t\le h\)。純軸の標準語長は
短語補題により \(u-2\) 以下。従って

\[
P_C\le B_{\rm cap}:=\binom h2+2u-3.
\tag{6}
\]

一般に二変数 downset の socle を y 指数昇順に
\((\alpha_i,\beta_i),\ 0\le i<s\) と並べると、
\(\alpha_i\ge i\)、\(\beta_i\ge s-1-i\)。よって次数 s−1 の全単項式
\(y^iz^{s-1-i}\) は標準で、その全 divisor も標準。従って

\[
\binom{\sigma_C+1}2\le P_C.
\tag{7}
\]

\(u=2h\) では \(B_{\rm cap}=\binom{h+4}2-9\)、
\(u=2h+1\) では \(B_{\rm cap}=\binom{h+4}2-7\)。従って (6)(7) より
\(\sigma_C\le h+2\)。式 (1)(2)(4) を合わせると

\[
\beta_1(G)\le B_{\rm cap}+(h+2)+1+
                (1+\lfloor u^2/4\rfloor-u).
\tag{8}
\]

target 最小容量 \(\binom u2+1\) と右辺の差は、偶数 u=2h なら
\(h(h-7)/2\)、奇数 u=2h+1 なら \((h^2-5h-2)/2\)。
前者は h≥7、後者は h≥6 で非負。従って **全 u≥13**、全 d、全 m を支払う。
実 target 幅 V=du は u 以上なので、\(F_1(m,V)\ge\binom V2+1\ge\binom u2+1\)。

## 6. 残る196 offset 組の全 m 上界

全 \(3\le u\le12\)、\(1\le a<b<u\)、\(\gcd(a,b,u)=1\) を列挙する。
各 core から \(P_C,\sigma_C,H_x\)、巡回 BFS から W を正確に求める。
F6 の既証明上界により、全 d≥1、全 m>du で

\[
R\le\widehat R:=\min\{W-u,\ u\max(H_x-2,0)\},
\quad \beta_1(G)\le U_1:=P_C+\sigma_C+1+\widehat R.
\tag{9}
\]

実行可能な自己完結 checker：

`python simplification_search/n4/check_shorter_n4.py`

歴史的 checker/certificate は import しない。次数 d の到達 offset 集合
\(E_d\) を \(E_0=\{0\}\)、\(E_d=E_{d-1}+\{0,a,b,u\}\) で直接計算する。
内部語の次数・offset を \((d,n)\) とすると endpoint 表示が存在する必要十分条件は
\(n\in E_{d-1}\) または \(n-u\in E_{d-1}\)。
短語補題により d≤u−2 を調べれば D を尽くす。コードは d=u−1 も空であることを
回帰確認する。異なる内部語の同次数・同 offset はないので、D から
\(P_C\)、socle、\(H_x=\max_D\{s+t-\lfloor(as+bt)/u\rfloor-
\boldsymbol1_{(as+bt)\bmod u>0}\}\) をそのまま得る。

| u | offset 組数 | 最小 \(\binom u2+1-U_1\) |
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

不足するのは \((u,a,b)=(3,1,2),(4,1,3)\) だけ。
前者は \(P_C=3,\sigma_C=2,H_x=0,\widehat R=0,U_1=6\)、
後者は \(P_C=5,\sigma_C=2,H_x=1,\widehat R=0,U_1=8\)。
\(d\ge2\) では target 幅 V がそれぞれ6以上・8以上なので最小容量16・29が支払う。
\(d=1,u=3\) は source=target。
\(d=1,u=4,(a,b)=(1,3)\) だけ次の短い現行 patch を残す。

## 7. 最後の幅4 patch と資格

現行 B2–B4 による正確な初期 ideal の計数を使用する。
m=6 は \(\mu(J)=6<F_1=9\)。m>6 では

| m mod4 | \(\mu(J)\) | actual \(F_1(m,4)\) |
|---:|---:|---:|
|0|6|7|
|1|8|10|
|2|8|9|
|3|6|8|

従って全 m≥6 で成立する。ここで一様最小容量7だけを使って
\(\mu(J)\le7\) と主張してはいけない。実際、初期 ideal の生成元数は8になり得る。
幅4だけの明示 core basis・純 v 閾値計算を残すのが確実で読みやすい。

checker は 196 行の JSON 証明書と三つの正係数多項式を出力する。
今回の実行で全比較が再現された。有限 m を一つも列挙せず、全称性は
(1)–(9) と幅4の剰余別証明から従う。

これは現行の任意体性と computational proof という資格を保った置換案である。
Savchev–Chen を不要にする一般補題、196 offset の紙上消去、幅4 patch の新しい
一行証明は、この探索では得ていない。現行本文への反映は別の編集作業とする。
