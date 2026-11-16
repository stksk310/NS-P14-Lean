# N4 基礎監査：actual endpoint 模型と二変数 Artin 移行

## 0. 監査結論と対象

以下の条件で、R24-N01 の端点模型と R39 の actual source 移行は正しい。

\[
0<a<b<u,\qquad d\ge1,\qquad m>du,\qquad
\gcd(m,d)=\gcd(a,b,u)=1,
\]
\[
\Gamma=\langle m,m+da,m+db,m+du\rangle,
\quad S=k[x,y,z,v],\quad E=k[x,v],\quad T=k[y,z].
\]

体 \(k\) は任意である。以下の証明は実際には \(m>u\) まで適用できるが、本監査の結論に必要なのは上記の true narrow 領域だけである。\(m>du\) により全生成元は相異なる \([m,2m)\) 内にあり、真正最小生成系である。生成元全体の gcd は \(\gcd(m,d)=1\) なので数値半群である。

監査対象原文は次である。

- `source_material/NS_WIDTH_P14_CANONICAL_PROOF_HANDOFF_R01_R57_20261109/04_HISTORICAL_THEOREMS/R24_LITERAL_PROOFS.md` の ORIGINAL R24_N01、特に §§2–6。
- `proof/sources/R39/R39_ACTUAL_SOURCE_CORE_TRANSFER.md` の §§2–4。

R25 の graph、TU、c2 などは一切使用しない。上界の比較先となる区間完備化公式も本基礎証明の入力ではない。

原文の実質的誤り・反例は見つからなかった。ただし R39 §4 の「最後の第二座標」は並べ順を明記すべきである。本稿では常に **第一座標を昇順に並べ、最後の第二座標＝最小の第二座標** とする。その corner 補題には純粋な \(v\) 冪の存在が必要であり、これも下で証明する。R24 の停止式は \(d=1\) の式として正しく、\(d>1\) への移行では長さ差を \(j\) とせず \(jd\) とする。

## 1. 数値半群の次数付き単項式基底

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

## 2. 端点座標と有限個の \(M_r\)

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

## 3. competition と clamp の必要十分性

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

## 4. 全 competition の証明付き停止式

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

## 5. \(P,R\) の有限計数と端点 Koszul 長さ

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

## 6. actual socle の \(m,d\) 一様上界

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

## 7. 二変数 Artin 商、\(\sigma\) の有限計算

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

## 8. actual kernel を保持した \(S\)-Betti 上界

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

## 9. 全標数・有限停止の範囲

本証明は任意の固定体 \(k\) 上で成立する。\(M,N,P,R,P_C,\sigma\) は単項式基底と整数の包含で決まる。核の単項式性と socle の基底性を証明したため、係数の相殺による標数の例外はない。actual \(G\) の全 \(S\)-Betti 数そのものの標数非依存性は主張しないし、必要でもない。spectral sequence と Tor 完全列の不等式を各体上でそれぞれ適用する。

計算の停止理由は次の通りである。

1. \(M_r\)：内部語長 \(u-1\) 以下の有限列挙、prefix 消去により完全。
2. \(T_r\)：\(j\le\lfloor(u-2)/2\rfloor+u/\gcd(m,u)\)、第4節により完全。
3. \(N_r\)：有限生成イデアルの交わりなので generator 対ごとの lcm で完全。
4. \(P,R\)：生存する極小 generator と隣接 corner の有限個数。
5. \(P_C,\sigma\)：有限 Artin 基底とその二つの乗法の有限計数。

これにより任意の \(m,d\) を受け取る有限 algorithm が得られる。「有限個の \(m,d\) を試して全称結論に外挿する」という論法ではない。

## 10. 独立回帰の内容と限界

`check_endpoint_model.py` は上の整数対式を直接実装した検算であり、既存 checker を import しない。別ルートで数値生成元の最大 order DP を実行し、次数基底の生存条件と端点 socle を照合する。また和集合 \(S_n\) から
\[
Q_n=S_n\setminus(S_{n-1}\cup(S_{n-1}+u))
\]
を独立に再構成し、極小点リストと照合する。

実行コマンド：

```sh
python n4_work/endpoint_model/check_endpoint_model.py --max-u 10 --max-d 3 --m-excess 5 --degree 12
```

`verification.json` の結果は PASS。\(3\le u\le10\)、\(1\le d\le3\)、\(du<m\le du+5\) の gcd 条件を満たす1308 source で、730272 個の数値基底を照合した。\(\gcd(m,u)>1\) も含む。停止式の後をさらに3周期生成しても \(T,N\) は変わらず、全例で \(R\le\widehat R\) となった。

例えば R24 の \((a,b,u,m,d)=(1,4,5,7,1)\) では
\[
(P_C,P,R,\sigma,W,H_x)=(7,5,0,2,7,2),
\]
非零 socle の例 \((1,9,10,14,1)\) では
\[
(P_C,P,R,\sigma,W,H_x)=(17,11,5,2,26,7)
\]
となった。有限検算は普遍定理の証明ではない。全 \(m,d\) と全標数を保証する根拠は第1–9節の証明である。
