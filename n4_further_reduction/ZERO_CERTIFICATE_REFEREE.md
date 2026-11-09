# Independent referee audit: eliminating the N4 196-row certificate

## Finding

**No mathematical blocker was found.** The arguments in `UNIFORM_SEARCH.md` and
`SMALL_WIDTH_SEARCH.md`, together with the existing algebraic width-four
boundary argument in V02 §14.6, replace every use of the 196-row offset
certificate in the N4 proof. This is a certificate-free proof of the N4
comparison conditional on the already proved common endpoint lemma and the
published inputs stated in V02. It is not a claim that the other parts of P14
are free of finite certificates, nor that the proof has no finite algebraic
case distinctions.

V02 was preserved. This report audits the new argument; the historical JSON
certificate is not used as a premise.

## 1. Uniform hypotheses and the target

Fix exactly the hypotheses (N1): arbitrary field, `0<a<b<u`,
`gcd(a,b,u)=gcd(m,d)=1`, `d>=1`, and `m>=du+2`. These imply `m>u`, so every
hypothesis needed by §12 is available. In particular, for the original
orientation and every such `m,d`,

\[
\beta_1(G)\le P_C+\sigma_C+1+R,\qquad
R\le\min\{W-u,u\max(H_x-2,0)\},\qquad
W\le1+\lfloor u^2/4\rfloor.
\]

No Cohen--Macaulay assertion, source Betti reflection, or `gcd(m,u)=1`
assumption enters. The target has **physical width** `V=du`, and the actual
interval formula gives

\[
F_1(m,V)\ge L_1(V)=\binom V2+1\ge L_1(u).
\]

Thus each numerical comparison below with `L_1(u)` is uniform in all allowed
multiplicities and dilations. For `u=3,4` the remaining cases with `d>=2` are
also paid by this same actual target formula, as described in §5 below.

The existing higher-row argument in V02 §14.4 uses no 196-row table. Its
bounds and the target comparisons remain applicable, including the separate
`u=3,4` treatment. Therefore the new work needs to replace only the old
first-row offset audit.

## 2. Structural counting and the published mixed-word input

The three identities

\[
y^b=x^{b-a}z^a,\quad
z^{u-a}=y^{u-b}v^{b-a},\quad
y^{u-b}z^a=x^{u-b}v^a
\]

have equal degree and equal integer offset on their two sides. Each right
side contains an endpoint, with strictly positive endpoint exponent. They
therefore prohibit the corresponding monomial and all its multiples in the
standard-word downset `D`, over every field.

For `h=floor(u/2)` and `k=(u-b)+a`, the two axes have at most `2u-k-1`
points. The mixed triangle has `C(h,2)` points; its forbidden rectangle has
`C(h-k+2,2)` points if `k<=h`. This proves the exact shape upper bound used in
both new notes. Because

\[
k+\binom{h-k+2}{2}\ge h+1\quad(k\le h),
\]

and `k>=h+1` otherwise, the uniform consequence is

\[
P_C\le2u-h-2+\binom h2.
\]

There is no assumption that every point in the bounding shape survives.
Counting a superset is sufficient.

The bounds `sigma_C<=h+1` and `sigma_C<=k` are valid for every such downset.
For the first, mixed maximal points have distinct first coordinates in
`1,...,h-1`, and at most two additional maximal points are on the axes. For
the second, split the mixed maximal points into `s<u-b` and `s>=u-b`. The
first group has at most `u-b-1` members. In the second group the forbidden
rectangle forces `t<a`, so there are at most `a-1` members. Distinct second
coordinates bound that group. Adding the two possible axis points gives
`sigma_C<=u-b+a=k`.

The use of Savchev--Chen in V02 §14.3 has the required scope: it is a theorem
for arbitrary finite cyclic order, and is applied only to a zero-sum-free
sequence of length greater than `u/2`. A standard word yields such a
sequence, since any nonempty zero-sum subsequence can be replaced by an
endpoint product. After the unit change, a sum below `u` forces one of the
two distinct representatives to be `1` and the other to be `c>=2`. The
identity (N11) then forces its multiplicity `R_0<c`, and the displayed
inequality (N12) contradicts length greater than `u/2`. The unit change is
used only in this additive-combinatorial argument; it is not asserted to
preserve actual source Betti numbers or endpoint height.

Combining the new count, `sigma_C<=h+1`, and `R<=W-u`, the gaps from `L_1(u)`
are exactly

\[
\frac{h(h-5)}2\ (u=2h),\qquad
\frac{h^2-3h-2}2\ (u=2h+1).
\]

They close all `u>=9`; at `u=5`, `H_x<=u-3=2` instead gives `R=0` and
`beta_1<=7+3+1=11=L_1(5)`.

## 3. Width six: the height split is exhaustive

Here `P_C<=10`, `sigma_C<=4`, and `H_x<=3`. For `H_x<=2`, the bound is
`beta_1<=15<16=L_1(6)`.

If `H_x=3`, a standard monomial attaining this height must have degree four:
all standard degrees are at most `u-2=4`, while height is degree minus
`ceil(offset/u)`, which is at least one for a nonconstant word. The mixed
cutoff prohibits mixed degree four. Since `b>=2`, the pure word `z^4` has
`ceil(4b/6)>=2` and cannot attain height three. For `y^4`, height three
requires `ceil(4a/6)=1`, hence `a=1`. Since `y^b` is forbidden and `b<=5`,
standardness of `y^4` forces `b=5`.

For this sole residual pair, the identities `yz=xv`, `y^5=x^4z`, and
`z^5=yv^4` give `P_C<=9`, `sigma_C<=2`; `R<=W-6<=4`. Hence
`beta_1<=16=L_1(6)`. This split does not inspect any multiplicity or dilation.

## 4. Widths seven and eight: exhaustive gap classes

For `u=7`, the shape bound gives

\[
\beta_1\le23-k-E_3(k)+\min(4,k).
\]

This is at most `22` for `k=2,3` or `k>=5`. The only remaining value is
`k=4`, so `b-a=3` and the three possibilities are `(1,4),(2,5),(3,6)`.
For the two outer pairs the displayed pure orders are `4,2` and `2,4`:

- `(1,4)`: `y^4=x^3z`, `z^2=yv`;
- `(3,6)`: `y^2=xz`, `z^4=yv^3`.

There are at most five axis words and two mixed words, giving `P_C<=7`.
One exponent takes only two values, so `sigma_C<=2`. For `(2,5)`, `yz=xv`
and the general pure orders are both five, giving `P_C<=9`, `sigma_C<=2`.
With `R<=6`, these cases give at most `18<22`.

For `u=8`, the shape bound is

\[
\beta_1\le31-k-E_4(k)+\min(5,k).
\]

It pays `k=2,3` and `k>=7`. The residual values `k=4,5,6` have gaps
`b-a=4,3,2`. Listing `1<=a<k` and excluding precisely the pairs with
`gcd(a,b,8)>1` gives the following exhaustive lists:

| `k` | primitive pairs |
|---:|:---|
|4|`(1,5),(3,7)`|
|5|`(1,4),(2,5),(3,6),(4,7)`|
|6|`(1,3),(3,5),(5,7)`|

For `k=4`, pure order five in both coordinates follows respectively from

\[
y^5=x^4z,\ z^5=xyv^3;
\qquad y^5=x^3zv,\ z^5=yv^4.
\]

The general forbidden mixed words are `y^3z` and `yz^3`, respectively.
Thus the axes have at most nine points and the mixed part at most five,
so `P_C<=14`; `sigma_C<=k=4`. With `R<=9`, this gives `beta_1<=28<29`.

For `k=5`, the four short pure relations are `z^2=xv`, `z^2=yv`,
`y^2=xz`, `y^2=xv`, in the listed order. The other pure order is at most
five by the general identities. Consequently there are at most six axis
points and three mixed points: `P_C<=9`, `sigma_C<=2`, and `beta_1<=21`.

For `k=6`, the outer pairs have pure orders at most `3,7` and `7,3`,
directly from the general identities. There are at most nine axis points
and five mixed points, so `P_C<=14`; the short coordinate bounds
`sigma_C<=3`. This gives `beta_1<=27`. The middle pair `(3,5)` has `yz=xv`
and both pure orders five, so `P_C<=9`, `sigma_C<=2`, and `beta_1<=21`.

All these bounds use each original orientation. In particular the reflected
pairs are checked by their own displayed relations; no reflection property
of `H_x`, `R`, or the actual source is needed.

## 5. Lower widths and the retained actual boundary calculation

At `u=3`, there is only `(1,2)`. The explicit core quotient is
`k[y,z]/(y,z)^2`, so `(P_C,sigma_C,R)=(3,2,0)`. For `d=1`, source and actual
interval target coincide. For `d>=2`, `V>=6` and the source first-row bound
`6` is below `L_1(V)>=16`.

At `u=4`, the nonboundary pairs are `(1,2),(2,3)`. The endpoint identities
prohibit `y^2,z^2` in both cases. A downset in this two-by-two square has
`P_C+sigma_C<=5`: the full square has length four and socle one, while any
proper downset has length at most three and socle at most two. Since `R=0`,
`beta_1<=6<7=L_1(4)`.

The boundary pair `(1,3)` has `yz,y^3,z^3` prohibited, so `P_C<=5` and
`sigma_C<=2`; with `R=0`, `beta_1<=8`. If `d>=2`, then `V>=8` and
`L_1(V)>=29` suffices. Only `d=1`, `m>=6` needs V02 §14.6.

That retained patch is a universal algebraic calculation, not an offset
machine certificate. Its core standard columns are the free columns
`1,y,y^2,z` and the column `z^2` with `x` exponent zero. The stated degree
and offset comparison proves these columns independent and hence proves
the proposed core initial ideal. For a longer competitor of excess length
`j`, (N26) gives the strictly negative `x` threshold, since
`6-(m+4)<0`. The restricted anchor requires one more `v` than the free
anchor and creates no additional competition. Since
`ceil((jm-n)/4)` is nondecreasing in `j`, the first competitor gives the
exact cutoff. Thus the initial ideal (N27) is justified for **all** `m>=6`.

At `m=6`, six initial generators are below the actual target value nine.
For `m>6`, writing `m=4q+r` gives exactly the following symbolic table:

|`r`|`(theta_0,theta_1,theta_2,theta_3,theta_6)`|`mu(J)`|actual `F_1(m,4)`|
|---:|:---|---:|---:|
|0|`(q,q,q,q,q-1)`|6|7|
|1|`(q+1,q,q,q,q-1)`|8|10|
|2|`(q+1,q+1,q,q,q-1)`|8|9|
|3|`(q+1,q+1,q+1,q,q)`|6|8|

These are four symbolic residue classes, not four sampled multiplicities.
The target column is `6+D`, with `D=4-((m-1) mod 4)` from the actual interval
formula. The minimal-generator counts follow from the four strict cutoff
comparisons displayed in V02; they do not require computing any Betti
matrix. The resulting generator bound is valid over an arbitrary field.

## 6. Regression checks and remaining presentation work

An independent inline finite check verified the exceptional `k` sets,
primitive-pair lists, 23 displayed endpoint identities, and all four
symbolic width-four cutoff/target residue formulas. Every assertion passed.
The independent fiber script `small_width/verify_structural_bounds.py` also
passed: 997 primitive oriented pairs through width 20, all 196 historical
rows, all 48 width-five-through-eight pairs, and 17 additional circuits.
These checks confirm transcription and arithmetic only. None is the reason
the inequalities hold for unrestricted `u,m,d`.

To state the conclusion accurately in a future integrated version, replace
V02's claims that the N4 proof requires the 196-row audit, and cite these
structural arguments instead. Keep §14.6 (or its equivalent symbolic proof)
and the published mixed-word input explicit. The appropriate conclusion is:
**N4 requires no finite offset machine certificate; the historical 196 rows
are optional regression evidence.**

## 7. 日本語置換稿の転記監査（2026年11月9日）

`N4_PAPER_REDUCTION_JA.md` を上記監査と照合した。初稿では§1の仮定から
`d>=1` が脱落していたため指摘し、rootが「`m,d,u,a,b` を整数、`d>=1`」
と明記したことを確認した。これにより `V=du>=u` と共通端点補題の適用条件が
明示された。その他、(P1)–(P7)、幅6のheight分岐、幅7・8の全場合分け、
幅3・4の比較、V02 §14.6から保持した四剰余の値に転記誤りは認めなかった。
本稿は独立した置換証明であり、V02原稿および全体を統合したV03原稿の編集を
意味しない。数学的な追加修正事項はなく、この版の固定に異論はない。
