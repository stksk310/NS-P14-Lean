# N4 非primitive四生成元・true narrow枝の独立監査

2026-11-09。対象原文は `R27_LITERAL_PROOFS.md` L3905付近の
`R27_D01_OFFSET_GCD_COMPRESSION_ALL_WIDTH_JA.md`、SHA-256
`8c667fdefe6aa95284dcf0686bf997bcb8b75b366fe024b8471d749a02bb0b71`。
以下では正規化offsetを原文の大文字ではなく `a,b,u` と書く。

## 1. 結論と正確な仮定

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

## 2. 正規化された斉次環と二変数ideal

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

## 3. 最小内部語の長さはu−2以下：外部零和定理は不要

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

## 4. actual order競合はdずつ長さを増やす

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

## 5. P、R、sigmaの上界

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

## 6. 一般Koszul二重複体：実第二微分の完全rankは不要

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

## 7. actual interval targetの全行支払い

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
親agentが今回両公刊一次資料の該当箇所を直接照合し、この剰余変換と任意体の資格を確認した。
本subagent自身のarXiv新規取得はnetwork CONNECT 403で失敗したので、直接再読と混同しない。

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

## 8. 監査判定

この非primitive true narrow枝に、有限campaign依存または未解決のrank条件は残らない。
証明は任意体で成立する。
公刊target公式を標準入力として明示した上で、原D01-Bの全称支払いは独立に閉じる。
そのtarget公式そのものの新規な再証明は本監査の範囲外である。

原D01の全幅拡張を最終定理の前提にする必要もない。
最小DAGは「初等短語補題 → actual競合ideal → P/R/sigma上界 → 一般Koszul二重複体 →
公刊actual interval公式＋4本の正係数比較」である。
歴史的checker、過去の閉鎖宣言、R25-TU、primitive有限残余はこの枝の論理前提に含まれない。
