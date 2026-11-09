# 小例外族の自立証明：全 m、全標数、全 Betti 行

2026-11-09。対象は任意体 k と

\[
\Gamma=\langle m,m+1,m+w-1,m+w\rangle,
\qquad 3\le w\le10,\quad m\ge w+2.
\]

G は実半群環の接錐、T は actual interval completion
\(\langle m,m+1,\ldots,m+w\rangle\) の接錐とする。本稿は
\(\beta_i(G)\le\beta_i(T)\) を全 i について証明する。
全生成元は [m,2m) にあり最小、gcd(m,m+1)=1 なので対象は真正な数値半群である。

結論に必要な有限 Taylor rank 計算は **0 個**である。
w=4 は monomial initial quotient の Betti 数を全 m で明示し、w=5 は紙上上界で閉じる。
w=6..10 も直接列計数で閉じる。旧 R24-N02 の16 Taylor 証明書は別途独立再生して一致したが、
以下の証明には使わない。一般 ratio machinery、R24-N01、R25-K01、Savchev–Chen は本稿の前提ではない。

## 1. 使用する actual target の標準公式

\(b_0=w-((m-1)\bmod w)\in\{1,\ldots,w\}\) とすると

\[
 F_i=\beta_i(T)=i\binom w{i+1}+
 \begin{cases}
 (b_0+1-i)\binom w{i-1},&i\le b_0,\\
 (i-b_0)\binom wi,&i>b_0,
 \end{cases}\qquad 1\le i\le w. \tag{1}
\]

\(F_0=1\)、\(F_i=0\) for i>w。これは arithmetic sequence の接錐に対する標準公式であり、
本稿で残す唯一の対象固有の外部入力である。一次資料は
[Gimenez–Sengupta–Srinivasan, arXiv:1108.3203](https://arxiv.org/pdf/1108.3203), Theorem 4.1, p.14 と
[Herzog–Stamate, arXiv:1308.4644](https://arxiv.org/pdf/1308.4644), Proposition 2.5, p.8。
root が両一次資料で任意体性と actual tangent cone への適用を確認した。
前者の m=aw+b, 1<=b<=w に対し b_0=w-b+1 なので (1) と同じ式である。
特に

\[
F_1\ge\binom w2+1,\qquad F_i\ge i\binom w{i+1}. \tag{2}
\]

以下の source 証明は (1) 以外の歴史的証明書に依存しない。

## 2. 明示 offset Gröbner basis

w=t+1 と置く。w=3 は source=target なので、以下 t>=3 としてよい。
S=k[x,y,z,v], A=k[x,v]、変数の offset をそれぞれ 0,1,t,t+1 とする。
offset 環

\[
C=k[s,sU,sU^t,sU^{t+1}]
\]

の kernel には次の t+1 個が入る。

\[
y^t-x^{t-1}z,\quad yz-xv,\quad
x^{t-q}z^q-y^{t+1-q}v^{q-1}\quad(2\le q\le t). \tag{3}
\]

内部重み wt(y)=1, wt(z)=t-1, wt(x)=wt(v)=0 を先に比較し、
通常次数、任意の lex 順を続ける global monomial order を使う。
(3) の左項は右項より内部重みが大きい。候補先頭 ideal は

\[
J_0=(y^t,yz,x^{t-q}z^q:2\le q\le t). \tag{4}
\]

標準単項式は次の 2t-1 列である。

* 自由列 1,y,...,y^(t-1),z：係数環 A。
* 制限列 z^q, 2<=q<=t-1：係数環 A/(x^(t-q))。

これらの像の (degree,offset) は相異なる。実際、自由列の offset 剰余は
0,1,...,t で一意である。制限列 z^q の剰余は r=t+1-q であり、
offset tq+K(t+1) は自由列 y^r v^(K+q-1) とだけ一致し得る。
後者の最小次数は t+K、前者の次数は q+K+L<t+K なので一致しない。
異なる制限列同士も剰余が異なる。同じ列の L,K は (degree,offset) から一意。

したがって (3) による停止する除算の標準余りは C で線形独立であり、
(3) は完全 Gröbner basis、(4) は actual initial ideal である。
これは Hilbert series の一致だけによる議論ではない。

## 3. actual tangent cone の全競合と initial ideal

列基点 b の次数を c、offset を n と書く。標準単項式 x^L v^K b の実半群 weight は
(L+K+c)m+n+K(t+1)。この monomial が G で消える必要十分条件は、
ある j>=1 に対し、同じ weight が次数 L+K+c+j で表示できることである。

w=t+1 とし

\[
r_j=(n-jm)\bmod w\in[0,t],\quad
\kappa_j=(jm+r_j-n)/w,
\]
\[
a(r)=\begin{cases}r,&0\le r<t,\\1,&r=t,\end{cases}
\qquad \Delta_j=a(r_j)-c-\kappa_j-j.
\]

自由 anchor は y^r (r<t) または z (r=t) であるから、その競合条件は厳密に

\[
K\ge\kappa_j,\qquad L\ge\Delta_j. \tag{5}
\]

2<=r_j<t のときは短い anchor
z^(w-r_j) v^(K-kappa_j-(t-r_j)) もあり、条件は

\[
K\ge\kappa_j+t-r_j,\qquad
L\ge\Delta_j-(r_j-1). \tag{6}
\]

これらは十分条件だけでなく必要条件でもある。第2節の全標準列を、指定した offset に
おいて分類すると自由 anchor とこの一つの制限 anchor しかなく、
制限 anchor の x 指数が制限を超えた領域は自由 anchor が既に覆うからである。

(5),(6) の各閾値を0で切り上げた x,v 単項式で生成する ideal を I_b とする。
制限列には既存の x^(t-q) 制限を加える。すると

\[
J=J_0+\sum_b bI_b=\operatorname{in}(I_G). \tag{7}
\]

証明：J_0 の標準 monomial を比較すると、非禁止 monomial は最大 order がその次数に等しく、
同次数では相異なる実 weight を持つ。これは G の実半群基底である。
各禁止 monomial は G で0。よって (3) による除算後、kernel の非禁止余りは線形独立性で0となり、
逆包含も得られる。

ここで M=t(t-1)、phi_b=wc-n>=0 と置くと

\[
w\Delta_j=(wa(r_j)-r_j)-\phi_b-j(m+w),
\qquad wa(r)-r\le M. \tag{8}
\]

短い anchor の対応する反射値は w-r<w なので、(6) の x 閾値は常に負である。
正の x 閾値は j< M/(m+w)、従って

\[
j\le J_{\max}=\lfloor(M-1)/(m+w)\rfloor \tag{9}
\]

にしか現れない。I_b は必ず純 v 冪を含む：v^m の実 weight は x^(m+w) のそれに等しく、
後者は w だけ長いからである。したがって各 I_b は、純 v 冪一つと正の x 閾値群で生成される。

独立 checker の有限 competitor 範囲の正当化も記す。
p=w/gcd(m,w) とすると j->j+p で r は同じ、kappa は m/gcd(m,w) 増加し、
Delta は p+m/gcd(m,w) 減少する。j>J_max の通常閾値は全て純 v 冪であり、
短い anchor の v 閾値はそれより大きい。よって全競合は 1<=j<=J_max+p で尽くされる。

## 4. 全標数の列 filtration 上界

Q=S/J。列を deg_y+(t-1)deg_z が大きい順に加えると S-部分加群の filtration になる。
y,z による乗法は列重みを厳密に増すか0となるため、各非零因子は次数 shift を除き

\[
A/I_b\quad\text{又は}\quad A/(I_b+(x^{t-q})),\qquad y=z=0. \tag{10}
\]

proper な2変数 monomial ideal の極小生成数を mu とすると、隣接 corner の明示解消の全階数は
(1,mu,mu-1)。y,z の Koszul 解消を tensor した S-解消は

\[
(1,\mu+2,3\mu,3\mu-2,\mu-1). \tag{11}
\]

この議論は任意体で成り立つ。Tor 長完全列で因子を足すことで Q の各 Betti 数を上から評価できる。
empty 列は0因子であり、以下では各列に mu>=1 の非負予算を割り当てる。
そのため empty 列から負の寄与 -2 等を誤って引くことはない。

通常の Gröbner flat degeneration により、各体上で beta_i(G)<=beta_i(Q)。
有限体でも generic fiber は元の G の体拡大なので同じ不等式となる。

## 5. w=4 の全 m の明示 Betti 公式

t=3 の場合、m>=6、m+w>=10>M=6 なので正の x 閾値はない。
実際には第3節より、t=3,4 の双方で常に J_max=0 であり、
kappa_j=ceil((jm-n_b)/w) は j とともに増す。従って厳密に

\[
J(m)=J_0+(b v^{\theta_{n_b}}:b\text{ は全列}),\quad
\theta_n=\max(\lceil(m-n)/w\rceil,0). \tag{12}
\]

短い anchor は純 v 閾値を下げないので (12) には現れない。

m=6 では

\[
J=(v^2,zv,z^2,yz,y^2v,y^3)\subset k[y,z,v].
\]

3変数 Artin 商の極小生成数は6、socle 基底は yv,y^2,z の3個。
Koszul top=socle と Euler から beta(Q)=(1,6,8,3,0)。

m>6 では全 theta_0,theta_1,theta_2,theta_3,theta_6 が正であり

\[
J=J'+(xz^2),\quad
J'=(y^3,yz,z^3,v^{\theta_0},yv^{\theta_1},
y^2v^{\theta_2},zv^{\theta_3},z^2v^{\theta_6})\subset R=k[y,z,v]. \tag{13}
\]

theta_6<=theta_3<=theta_0 なので

\[
(J':z^2)=(y,z,v^{\theta_6}). \tag{14}
\]

最小 R-解消間で乗法 z^2 を lift し、全係数に x を掛ければ、
乗法 xz^2 の chain map は全 entry が (x) に入る。
従って

\[
0\to S/(J':z^2)(-\deg(xz^2))\xrightarrow{xz^2} S/J'\to Q\to0
\]

の mapping cone は任意体で **minimal** である。
mu=mu(J'), tau=dim socle(R/J') とすれば

\[
\beta_R(R/J')=(1,\mu,\mu+\tau-1,\tau),\qquad
\boxed{\beta_S(Q)=(1,\mu+1,\mu+\tau+2,\tau+3,1).} \tag{15}
\]

mu,tau の計数も紙上で尽きる。
J' の常在 generator は y^3,yz,z^3,v^(theta_0)。追加 generator はそれぞれ
theta_1<theta_0, theta_2<theta_1, theta_3<theta_0, theta_6<theta_3 のときだけ生じる。
socle は、各 y^a z^b 列の v-top のうち y,z で消えるものを数えればよい。
必ず y^2 と z^2 列から一つずつ、y 列から theta_1>theta_2 のとき、
z 列から theta_3>theta_6 のとき、定数列から theta_0>theta_1 かつ theta_0>theta_3 のときに一つ。
従って r=m mod4 により次の表になる。

|m|mu|tau|beta(Q)|actual beta(T), i=0..4|
|---|---:|---:|---|---|
|6|6|3|(1,6,8,3,0)|(1,9,16,9,1)|
|>6, r=0|5|3|(1,6,10,6,1)|(1,7,14,11,3)|
|>6, r=1|7|4|(1,8,13,7,1)|(1,10,20,15,4)|
|>6, r=2|7|4|(1,8,13,7,1)|(1,9,16,9,1)|
|>6, r=3|5|2|(1,6,9,5,1)|(1,8,12,7,2)|

各行で成分比較が成立する。これは有限 m の外挿ではなく (13)-(15) の全 m の明示公式である。

## 6. w=5 は rank 計算を要しない

t=4、M=12、m+w>=12 なので J_max=0、(12) が成立する。
y^r 列 r=0,1,2,3 の theta_r=ceil((m-r)/5) は、r とともに非増加で段差が高々一回。
従って y^r v^(theta_r) の極小 generator は高々2個。
z,z^2,z^3 列から高々3個、core は5個だから

\[
\beta_1(Q)=\mu(J)\le10. \tag{16}
\]

自由5列の mu 予算は各1、制限2列は各2、総予算 C=9、全列数 B=7。
(11) により beta_3(Q)<=3C-2B=13、beta_4(Q)<=C-B=2。
Q は非零 ideal による S の商なので Euler は
1-beta_1+beta_2-beta_3+beta_4=0 であり

\[
\boxed{(\beta_1,\beta_2,\beta_3,\beta_4)(Q)\le(10,22,13,2).} \tag{17}
\]

(1) を b_0=1,...,5 に代入した actual target の成分別最小値は (11,25,25,9)。
従って全 m>=7 で全行比較が成立する。

## 7. 6<=w<=10 の全 m：正の x 閾値の直接計数

以下 t=5,...,9。固定 j>=1 に対し jm=Q_j w+rho_j, 0<=rho_j<=t と書き、
d_j=t-Q_j-rho_j-j と置く。m>=w+2 なので Q_j>=j。
既存の x cap より小さい正閾値だけを数える。これは mu 予算を増す可能性のある全 generator を含む。

rho>0 のとき、y^r 列では r<=rho-2 でだけ正の通常閾値が可能で、その値は d。
r=rho-1 は competitor が z となり閾値は負、残りも負である。
z^q 列 (1<=q<=t-1) の通常閾値は厳密に

\[
\begin{cases}
d-q,&q+rho\le t+1,\\
\text{負},&q+rho=t+2,\\
d+t-q,&q+rho\ge t+3.
\end{cases} \tag{18}
\]

q>=2 の x cap は t-q、q=1 は自由である。

* rho>0,d>0：y 列は rho-1 個、z 列は高々 d-1 個。合計 t-Q_j-j-2 以下。
* rho>0,d=0：0個。
* rho>0,d<0：可能な z 列は t+3-rho<=q<=t+d-1。
  合計 max(t-Q_j-j-3,0) 以下。
* rho=0：y 列と z 列 q=1 は負。残りは 2<=q<=t-Q_j-j-1。
  合計 max(t-Q_j-j-2,0) 以下。

最後の branch では cap を超える閾値はそもそも redundant。
従って全 branch を合わせ、固定 j の個数は max(t-2j-2,0) 以下。
短い anchor は第3節により正の x 閾値を一切持たない。
全 j での予算を

\[
H_t=\sum_{j\ge1}\max(t-2j-2,0),\quad B=2t-1,\quad C=3t-3+H_t
\]

とする。各列に純 v 冪一つ、制限 t-2 列に x cap 一つを加えたものが C である。
(7),(11) から全 m で

\[
\boxed{\beta_1(G)\le3t+H_t,\quad\beta_2(G)\le3C,\quad
\beta_3(G)\le3C-2B,\quad\beta_4(G)\le C-B.} \tag{19}
\]

必要な t は5個だけで、(2) との比較は次の整数表で完了する。

|w|H_t|C|source 上界 i=1..4|target 下界 i=1..4|
|---:|---:|---:|---|---|
|6|1|13|(16,39,21,4)|(16,40,45,24)|
|7|2|17|(20,51,29,6)|(22,70,105,84)|
|8|4|22|(25,66,40,9)|(29,112,210,224)|
|9|6|27|(30,81,51,12)|(37,168,378,504)|
|10|9|33|(36,99,65,16)|(46,240,630,1008)|

i=0 は双方1、i>4 は source が四変数商なので0。これで指定範囲の全 m、全行、任意体が尽きる。

## 8. 旧16 Taylor 証明書の独立監査と周期性

これは上記証明に不要な、旧有限成分に対する追加監査である。
t=3,4 では全 n_b<=M=t(t-1)。m>M では (12) の追加 generator は全て正の v 指数を持ち、
m->m+w はその全指数を一律に1増す。core の v 指数0は固定。
この操作は可除関係と **全 subset の lcm 等号関係**を保存する。
よって Taylor 解消を k に tensor した複体の各 entry（lcm が等しいときだけ exterior sign、他は0）も同じ。
したがって beta(S/J(m)) は m>M で w-周期的。actual target も (1) により w-周期的である。

従って t3 は m6..10 の5点、t4 は m7..17 の11点で全 m を覆う、という旧16点還元は正しい。
コードは (12) から ideal を独立構築し、第3節の全 competitor 記述とも照合した。
旧 replay JSON は比較対象として読むだけで、生成器や rank の計算に使用しない。

座標ごとに正指数を大小順の rank に圧縮しても lcm 等号関係は保存される。
この圧縮により16点は10種類の Taylor 複体になる。
各境界で整数 +/-1 pivot のみを用いて消去し、零残余を確認した。
pivot は整数可逆操作なので全体で同じ rank。負対照 [2] は非零残余として拒否する。
各複体の全 generator/rank/pivot/Betti と16点の対応は certificate.json に収録した。

実行コマンド：

```bash
python3 n4_work/boundary_family/check_boundary_family.py \
  --legacy reduction_work/boundary_agent/legacy_b4_replay/r24_n02_replay.json \
  --regression --out n4_work/boundary_family/certificate.json
```

2026-11-09 の結果：PASS、旧16点一致、10 lcm classes、actual 最大 order の231点回帰一致。
231点は degree<=5 の独立 dynamic programming 回帰であり、無限量化の証明には数えない。
証明の全 m 性は第2–7節の紙上議論から来る。

## 9. 残る前提と監査判定

残る対象固有の前提は actual target の公刊公式 (1) だけである。
それ以外は Gröbner degeneration による Betti 上界、Koszul top=socle、
隣接 corner の2変数 monomial 解消、Tor 長完全列、minimal mapping cone という標準代数であり、
適用する写像・全列・全競合・全整数不等式は本文で示した。
Lean kernel による formal verification を実行したという主張ではない。

旧 R24-N02 の h=1 境界部分に、この監査で反例や周期性の欠落は検出しなかった。
旧16 Taylor を任意体で認証でき、さらに本稿によってその16個を必要祖先から除去できる。
N4 の第一行例外だけを使う場合は、w4 の表の beta_1、w5 の (16)、w6..10 の (19) の第一行だけを引用すれば足りる。
