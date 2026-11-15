### O-Large：大 rank の一つの調和障壁と一つの床比較

ここでは、前節の同じ資源列から得た上界を
\[
\begin{aligned}
a&=r(r+1)/2,\quad D=\lfloor a/2\rfloor+1,\quad
\alpha=(r-1)/(D+1),\quad H_D=\sum_{j=1}^{D}1/j,\\
U_r(e,\delta)
&=\alpha\delta\mathcal V+(r-1-\alpha)\delta
+\left(\frac{r+1}{2}-\alpha\right)(e+\delta-1-a)\\
&\qquad +(e+\delta-1)
 \left[(r-1)(H_D-3/2)-(D-2)\alpha\right],\\
G_r(e,\delta)&=\delta(\mathcal V+1)-U_r(e,\delta),\qquad
\mathcal V=e+\delta/2-3/2
\end{aligned} \tag{OL1}
\]
と書く。主張は、整数 \(r\ge9\)、\(e\ge10\)、\(\delta\ge a\) で
\(G_r(e,\delta)>0\) である。以下は実際には有理数 \(e,\delta\) にも成立する。
actual cut では \(e\ge r+1\)、\(\delta\ge a\) なのでこの範囲に入る。

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
(OL1) を整理すると
\[
g_0:=G_r(10,a)=(r-1)(a+9)(T_r-H_D). \tag{OL5}
\]
\(T_-(r)\) を \(T_r\) の最後の分母 \(2(D+1)(a+9)\) を
\((a+3)(a+9)\) に置き換えた式とする。(OL2) より
\(T_-(r)\le T_r\)。さらに
\[
T_-(r)-B(r)=
\frac{r^3[(r-10)(2r+15)+2]
+r[111(r-10)+210]+972}
 {2r(r-1)(r^2+r+6)(r^2+r+18)}>0 \quad(r\ge10). \tag{OL6}
\]
よって \(H_D<B(r)<T_-(r)\le T_r\) から \(g_0>0\)。
残る \(r=9\) は \(a=45,D=23\) を (OL1) に入れた正確な値
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
(OL1) から得る恒等式は
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
任意の有理数 \(s,t\ge0\) に対して、固定 cutoff の共通差分恒等式を
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

---

#### 編集・形式化対応（本文へ統合する際はこの末尾を台帳へ移す）

- 固定入力：commit `345e2d82fea50ef89e00a8f35c4fb53ac601d7ce` の
  `NSP14/Ordinary/LargeSeed.lean`、`LargeScalar.lean`、
  `SmallScalar.lean`、`docs/LEAN_PAPER_ALIGNMENT_JA.md` A05/A06。
- (OL1) の上界は `NSP14.Ordinary.SmallScalar.upper`、差は同 `gap`。
  資源列との接続は `NSP14.Ordinary.SmallScalar.Resources.scalar_lt_large`。
- (OL2)–(OL6)：`NSP14.Ordinary.LargeSeed.cutoff_bounds`, `cutoff_step`,
  `harmonic_cutoff_step`, `barrier_step_identity`, `harmonic_lt_barrier`,
  `threshold_gap_identity`, `thresholdLower_le_threshold`, `seed_eq_threshold`,
  `rank_nine_seed`, `large_seed_pos`。
- (OL7)–(OL9)：`NSP14.Ordinary.LargeScalar.seed_slope_identity`, `step_identity`,
  `correction_neg`, `baseSlope_pos`, `floor_comparison_identity`, `floorStep_gt`,
  `baseStep_gt`, `quadrant_identity`, `gap_pos_shift`, `large_gap_pos`。
- 採用状態：すべて既存 Lean で証明済みの経路を紙上へ展開したもの。
  この担当で新しい数学的仮定・新しい形式化義務は導入していない。
  今回は Lean 再実行をしておらず、形式化状態はソースを読んだ範囲の記録。
- 実質削減：旧 V02 (S14)、(S17)–(S19) の凸性と中間 \(2/r\) 比較を
  (OL3)–(OL4) へ置換。旧 F₀/F₁ の床偶奇分岐を (OL8) 一式へ置換。
  付録へ移した削減ではない。
- 手元の独立代数照合：SymPy で (OL4)、(OL5)、(OL6)、(OL7) 二式、
  (OL8)、(OL9) の差を有理関数として零へ約分。
  Python `Fraction` で二つの seed の厳密値を照合。
  この検算は恒等式の転記確認であり、全称性は上記の正係数分解・帰納法・符号証明による。
