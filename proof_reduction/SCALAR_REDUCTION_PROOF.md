# P14 scalar 部：全 actual r に直接適用する e>=10 の短い証明

## 結論

cutoff を \(D=\lfloor\delta/2\rfloor+1\) とし、既存の一列の上界に
\(H_1\le M-a_r\) を保持する。このとき **全ての整数**

\[
 e\ge10,\qquad r\ge4,\qquad\delta\ge a_r=\frac{r(r+1)}2
\]

について、改善gapは狭義に正である。
したがって actual cut の \(r\) へ直接適用でき、\(p(\delta)\) や最大rankへの数値包絡は不要である。
\(\delta\ge210\) を別扱いする調和数帰納も不要である。
必要な有限算術は \(\mathcal H_{23}<747/200\) の1個、
小さな有理式7個、非負係数の多項式恒等式1個である。

以下は scalar の独立証明である。既存のPASS値を根拠にしない。
半群構造、資源列の不等式、targetへの移行は別途必要である。

## 1. cutoff を残した同じ資源列の上界

\[
 M=e+\delta-1,\quad V=e+\frac\delta2-\frac32,\quad
 \mathcal H_D=\sum_{u=1}^D\frac1u,
\]
\[
 \alpha=\frac{r-1}{D+1},\quad c=\frac{r+1}2-\alpha,
 \qquad D=\lfloor\delta/2\rfloor+1.
\]

ここで \(D\ge6\)、\(D\ge r\)、\(\alpha<1\)、\(c>0\) である。
\(D\ge r\) は \(D\ge\lfloor a_r/2\rfloor+1\ge r\) から従う。

既存の scalar

\[
 F_r=(r-1)\delta+\frac{r+1}2H_1+
                 \sum_{t\ge2}\frac{r-1}{t+1}H_t
\]

に対して、\(t\ge D\) の重みを \(\alpha\) で評価する。
\(H_0=\delta\)、\(\sum_tH_t\le\delta V\)、\(H_t\le M\)、
\(H_1\le M-a_r\) により

\[
\begin{aligned}
F_r\le\widehat U_r={}&\alpha\delta V+(r-1-\alpha)\delta
 +c(M-a_r)\\
 &+M\sum_{t=2}^{D-1}\left(\frac{r-1}{t+1}-\alpha\right).
\end{aligned}
 \tag{1}
\]

この有限和を足すと

\[
 \widehat U_r=M+(r-1)K_D-ca_r,
\]
\[
 K_D=\delta+\frac{\delta(V-1)}{D+1}
       +M\left(\mathcal H_D-2+\frac2{D+1}\right).
 \tag{2}
\]

同じ資源列の \(H_1\) の正の係数の上界を置き換えたものであり、
\(H_1\) を二重に消費していない。

以下、\(D\) を一時的に独立変数とし、

\[
 G_r(e,d;D)=d(V+1)-\widehat U_r,
 \qquad D(d)=\lfloor d/2\rfloor+1
\]

と書く。\(G_r(e,d;D)\) の \(e\) の係数は

\[
 A_r(d;D)=d-1-(r-1)\left(\mathcal H_D-2+\frac{d+2}{D+1}\right).
 \tag{3}
\]

\(G_r(10,d;D(d))>0\) と \(A_r(d;D(d))>0\) を示せばよい。

## 2. 三角数基点を調和数閾値へ

固定した \(r\ge4\) について \(a=a_r\)、\(D_0=D(a)\) と置く。
\(e=10,d=a\) では \(M=a+9,V=(a+17)/2\) だから、直接整理により

\[
 G_r(10,a;D_0)=(r-1)(a+9)(T_r-\mathcal H_{D_0}),
\]
\[
 T_r=\frac{a(a+22-r)}{2(r-1)(a+9)}+\frac{2r-3}{r-1}
       -\frac{a(a+21)+36}{2(D_0+1)(a+9)}.
 \tag{4}
\]

全ての \(r\ge4\) で \(\mathcal H_{D_0}<T_r\) を示す。

## 3. 唯一の調和数アンカーと6基点

\[
 \mathcal H_{23}=\frac{444316699}{118982864}<\frac{747}{200},\qquad
 \frac{747}{200}-\mathcal H_{23}=\frac{2107451}{2974571600}>0.
 \tag{5}
\]

\(D\le23\) なら、Cauchy の不等式、または算術平均・調和平均から

\[
 \sum_{u=D+1}^{23}\frac1u\ge\frac{2(23-D)}{D+24}.
\]

実際、項数 \(k=23-D>0\) のとき分母の総和は \(k(D+24)/2\) であり、
\((\sum1/u)(\sum u)\ge k^2\) を使う。\(k=0\) のときも両辺0である。
従って

\[
 \mathcal H_D<\frac{747}{200}-\frac{2(23-D)}{D+24}.
\]

以下の6個の正の有理数だけで \(4\le r\le9\) が閉じる。

| \(r\) | \(D_0\) | \(T_r\) | \(T_r-747/200+2(23-D_0)/(D_0+24)\) |
|---:|---:|---:|---:|
| 4 | 6 | \(1126/399\) | \(17587/79800\) |
| 5 | 8 | \(35/12\) | \(143/1200\) |
| 6 | 11 | \(623/200\) | \(23/350\) |
| 7 | 15 | \(745/222\) | \(2993/96200\) |
| 8 | 19 | \(622/175\) | \(321/60200\) |
| 9 | 23 | \(269/72\) | \(1/900\) |

## 4. rank 方向の帰納

\(\varepsilon_r=a_r-2\lfloor a_r/2\rfloor\in\{0,1\}\) とし、

\[
 T_\varepsilon(r)=\frac{a(a+22-r)}{2(r-1)(a+9)}+\frac{2r-3}{r-1}
       -\frac{a(a+21)+36}{(a+4-\varepsilon)(a+9)}.
\]

すると \(T_r=T_{\varepsilon_r}(r)\)、かつ
\(T_1(r)\le T_r\le T_0(r)\) である。
付録の正係数恒等式から

\[
 T_1(r+1)-T_0(r)>\frac2r\qquad(r\ge10).
 \tag{6}
\]

一方、\(b=D(a_{r+1})-D(a_r)\le(r+2)/2\)、
\(D(a_r)+1\ge(a_r+3)/2\)、\(D(a_{r+1})\ge(a_{r+1}+1)/2\) である。
\(u\mapsto1/u\) の凸性から、端点を結ぶ直線以下の値を足すと

\[
\begin{aligned}
 \mathcal H_{D(a_{r+1})}-\mathcal H_{D(a_r)}
 &\le\frac b2\left(\frac1{D(a_r)+1}+\frac1{D(a_{r+1})}\right)\\
 &\le\frac{r+2}2\left(\frac1{a_r+3}+\frac1{a_{r+1}+1}\right)
 <\frac2r.
\end{aligned}
 \tag{7}
\]

最後の差は

\[
 \frac{8(r^2+3r+6)}{r(r^2+r+6)(r^2+3r+4)}>0.
\]

残る \(r=9\to10\) は \(D(a_9)=23,D(a_{10})=28\) に対して

\[
 \mathcal H_{28}-\mathcal H_{23}
 \le\frac52\left(\frac1{24}+\frac1{28}\right)
 =\frac{65}{336}<\frac15,
\]
\[
 T_{10}-T_9-\frac15=\frac{293}{18560}>0.
 \tag{8}
\]

従って第3節と帰納により、全ての整数 \(r\ge4\) で

\[
 G_r(10,a_r;D(a_r))>0.
 \tag{9}
\]

## 5. slope は d とともに増える

固定した \(r\ge4\) に対し \(d\ge a_r\) とする。
\(n=D(d)\)、\(\alpha_n=(r-1)/(n+1)\) と書く。
(3) を直接差し引くと、偶数 \(d\) から奇数へは

\[
 A_r(d+1;D(d+1))-A_r(d;D(d))=1-\frac{r-1}{n+1}>0,
\]

奇数 \(d\) から偶数へは

\[
 A_r(d+1;D(d+1))-A_r(d;D(d))
 =1-\frac{2(r-1)}{(n+1)(n+2)}>0.
 \tag{10}
\]

いずれも \(n\ge r\) を使った。従って chosen cutoff の slope は増加する。
また \(\alpha_{D(d)}\) は非増加である。

## 6. 基点正性から gap の全 d 単調性と正 slope へ

\(a=a_r\)、\(D_0=D(a)\)、\(A_0=A_r(a;D_0)\) とする。
直接整理すると

\[
 G_r(10,a;D_0)=(a+9)A_0+C,
\]
\[
 C=\frac{a[-a(D_0-r+2)-D_0(r-4)+3]}{2(D_0+1)}<0.
 \tag{11}
\]

\(D_0\ge r\)、\(a\ge10\)、\(r\ge4\) により括弧は高々 \(-2a+3<0\) である。
(9), (11) から

\[
 A_0>\frac{-C}{a+9}>0.
 \tag{12}
\]

cutoff \(D=n\) を固定して \(d\) を一つ増やす差は

\[
 G_r(10,d+1;n)-G_r(10,d;n)
 =A_r(d;n)+11-r-\frac{8(r-1)}{n+1}.
 \tag{13}
\]

(10), (12) と \(n\ge D_0\) により、(13) は

\[
 F_\varepsilon:=\frac{-C}{a+9}+11-r-\frac{8(r-1)}{D_0+1}
 \tag{14}
\]

より大きい。ただし \(\varepsilon=a-2\lfloor a/2\rfloor\in\{0,1\}\)、
\(D_0=(a-\varepsilon)/2+1\) である。
\(F_\varepsilon\) を \(a,r\) の有理式とみなすと、直接通分により

\[
 F_0-F_1=\frac{(r-1)(a^2+17a+144)}{(a+3)(a+4)(a+9)}>0,
\]
\[
 F_1=\frac a2-\frac{3r}2+\frac{11}2
       +\frac{3(5r+31)}{2(a+9)}-\frac{17(r-1)}{a+3}.
 \tag{15}
\]

\(r\ge4\) に対して

\[
 \frac a2-\frac{3r}2+\frac{11}2
 =\frac{r^2-5r+22}4\ge\frac92,
\]
\[
 a+3-4(r-1)=\frac{(r-3)(r-4)}2+1>0.
\]

従って

\[
 F_\varepsilon\ge F_1>\frac92-\frac{17}4=\frac14.
 \tag{16}
\]

偶数 \(d\) からのstepでは cutoff は変わらないので、(13), (16) で gap が増える。
奇数 \(d=2n-1\) からは、まず cutoff \(n\) のまま \(d+1=2n\) に増やし、
次に cutoff を \(n+1\) に増やす。後者による追加差は

\[
 G_r(e,2n;n+1)-G_r(e,2n;n)
 =\frac{r-1}{(n+1)(n+2)}\,[n(e-4)+a_r]>0
 \quad(e\ge10).
 \tag{17}
\]

よって \(G_r(10,d;D(d))\) は \(d\ge a_r\) で毎step \(1/4\) より大きく増加する。
(9) と合わせ全域で正であり、(10), (12) から slope も全域で正である。
最後に

\[
 G_r(e,d;D(d))=G_r(10,d;D(d))+(e-10)A_r(d;D(d))>0
 \qquad(e\ge10).
 \tag{18}
\]

これが結論である。actual \(r\) に直接使えるので、最大rankへの包絡は不要。

## 付録：rank差分補題 (6) の正係数恒等式

直接通分すると

\[
 T_1(r+1)-T_0(r)-\frac2r=\frac{P(r)}{Q(r)},
\]
\[
\begin{aligned}
 P(r)={}&r^{10}-r^9-18r^8-426r^7-1543r^6-10513r^5\\
        &-22712r^4-78276r^3-27568r^2-57088r+175104,
\end{aligned}
\]
\[
 Q(r)=4r(r-1)(r^2+r+8)(r^2+r+18)(r^2+3r+8)(r^2+3r+20)>0.
\]

\(t=r-10\ge0\) と置けば

\[
\begin{aligned}
 P(t+10)={}&t^{10}+99t^9+4392t^8+114534t^7+1934237t^6\\
 &+21934307t^5+167027138t^4+823740244t^3\\
 &+2388816952t^2+3111610752t+37151424>0.
\end{aligned}
\]

これは整数係数の恒等式であり、調和数や無限の数値検算を含まない。
付属 `checks/verify_scalar.py` は定義式から有理多項式を構成し、
(E3相当の) 通分後の全係数一致と、この平行移動後の全係数一致を厳密に検査する。

## 独立検証コード

`checks/verify_scalar.py` は (5)、第3節の6個の正有理式、(8) の1個、付録の係数恒等式を再計算する。
`--diagnostic N` は更に \(10\le\delta\le N\)、\(r=p(\delta)\) において、
元の重み付き上界 (1) とgapの恒等式、slopeの差分、固定cutoffのgap差分、
cutoff増加差分、基点の \(C,F_\varepsilon\) の恒等式を全て厳密有理数で独立診断する。
診断は紙上の普遍帰納の代わりではない。

独立数学レビューでも、上界・threshold・rank帰納の多項式全係数・delta差分を再導出し、式誤りや量化の穴は見つからなかった。診断コードは各deltaの最大許容rankだけを検査し、全許容組を列挙するものではない。全actual rankの主張は本稿の帰納証明による。
