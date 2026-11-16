# N4: structural replacement for the 196 offset checks

This is an independent research note. The manuscript and its certificates are
unchanged. The arguments below use the already proved endpoint bounds (N4)–(N5),
the distance-sum bound (N8), the antichain argument in (N9), and the mixed-word
cutoff (N13). They prove the first-row comparison for every normalized width
`u >= 5` by inequalities and a few explicitly displayed relations. The known
`u=3` identity and width-four boundary patch can then be retained.

The global counting lemma was found in this task. The compact `u=7,8` case
organization was proposed by the root agent and audited here. No new external
theorem is used.

## 1. A stronger global count

Write `h=floor(u/2)`, `r=u-b`, `s=a`, and `k=r+s=u-(b-a)`. Thus `2 <= k <= u-1`.
The following equal-degree, equal-offset identities hold in the homogeneous
endpoint model:

\[
y^b=x^{b-a}z^a,\qquad
z^{u-a}=y^{u-b}v^{b-a},\qquad
y^{u-b}z^a=x^{u-b}v^a.                 \tag{S1}
\]

Each right side contains an endpoint. Consequently standard pure axes have at
most `b` and `u-a` monomials respectively, including their common unit, and the
orthant above `(r,s)` is excluded from `D`. The two axes therefore contribute at
most `2u-k-1` words. The mixed-word cutoff gives at most `C(h,2)` mixed words.
If `k <= h`, the excluded orthant removes exactly `C(h-k+2,2)` points of that
mixed triangle. Hence

\[
P_C\le 2u-k-1+\binom h2-E_h(k),\qquad
E_h(k)=\begin{cases}\binom{h-k+2}{2},&k\le h,\\0,&k>h.\end{cases}       \tag{S2}
\]

For `k<=h`, use `C(h-k+2,2) >= h-k+1`. For `k>=h+1`, use `k>=h+1` directly.
Both cases give the uniform improvement

\[
\boxed{P_C\le 2u-3+\binom{h-1}{2}.}                   \tag{S3}
\]

There are at most `h-1` mixed socle points: their first coordinates are distinct
integers from `1` through `h-1`. At most two additional socle points lie on the
pure axes. Thus `sigma_C<=h+1`. There is a second useful bound. If
`sigma_C>=k+1`, the existing antichain argument forces every degree-`k` word
into `D`, contradicting the third relation in (S1). Therefore

\[
\boxed{\sigma_C\le\min(h+1,k).}                       \tag{S4}
\]

Use (S3), `sigma_C<=h+1`, and `R<=W-u<=1+floor(u^2/4)-u` in (N5). They give

\[
\beta_1(G)\le\binom h2+u+1+\lfloor u^2/4\rfloor.      \tag{S5}
\]

Subtracting this upper bound from `L_1(u)=C(u,2)+1` gives

\[
\begin{cases}
h(h-5)/2,&u=2h,\\
(h^2-3h-2)/2,&u=2h+1.
\end{cases}                                           \tag{S6}
\]

The even expression is nonnegative for `h>=5`; the odd expression is positive
for `h>=4`. This proves every `u>=9`, including `u=10` at equality. Since
`V=du>=u`, the actual target is at least `L_1(u)`. No offset, multiplicity, or
`d` enumeration occurs in this proof.

## 2. Widths five and six

For `u=5`, the existing height bound gives `H_x<=u-3=2`, so `R=0`. The new
count gives `P_C<=7` and (S4) gives `sigma_C<=3`. Consequently

\[
\beta_1(G)\le7+3+1=11=L_1(5).
\]

For `u=6`, the bounds are `P_C<=10`, `sigma_C<=4`, and `H_x<=3`. If `H_x<=2`,
then `R=0` and `beta_1<=15<16=L_1(6)`. If `H_x=3`, a standard word attaining
that height must have degree four, since every nonconstant word has
`ceil(offset/u)>=1`. Mixed degree four is prohibited. A pure `z^4` has offset
`4b>=8` and height at most two. A pure `y^4` of height three requires `a=1`;
the first relation in (S1) then forces `b=5`. Thus the only remaining pair is
`(a,b)=(1,5)`. For this pair,

\[
yz=xv,\qquad y^5=x^4z,\qquad z^5=yv^4.
\]

There are no mixed standard words, so `P_C<=9` and `sigma_C<=2`. Also
`R<=W-6<=4`. Hence `beta_1<=9+2+1+4=16=L_1(6)`.

## 3. Width seven: three relations in one exceptional gap

Here `h=3`, `W<=13`, and `R<=6`. From (S2) and (S4),

\[
\beta_1(G)\le23-k-E_3(k)+\min(4,k).
\]

For `k=2,3`, this is at most `20,22` respectively. For `k>=5`, it is at most
`27-k<=22`. Thus only `k=4`, equivalently `b-a=3`, remains. Its three possible
pairs are `(1,4),(2,5),(3,6)`.

For `(1,4)`, the relations `y^4=x^3z` and `z^2=yv` give pure caps `4,2`.
For `(3,6)`, `y^2=xz` and `z^4=yv^3` give pure caps `2,4`. In both cases there
are at most five axis words and at most two mixed words of degree at most
three. Thus `P_C<=7`. Containment in a rectangle with one side two gives
`sigma_C<=2`, and `beta_1<=7+2+1+6=16`.

For `(2,5)`, `yz=xv`, so (S1) gives `P_C<=5+5-1=9` and `sigma_C<=2`. Therefore
`beta_1<=18`. All cases are below `L_1(7)=22`.

## 4. Width eight: three exceptional gaps

Here `h=4`, `W<=17`, and `R<=9`. The structural bound is

\[
\beta_1(G)\le31-k-E_4(k)+\min(5,k).
\]

It is at most `25` for `k=2`, at most `28` for `k=3`, and at most
`36-k<=29` for `k>=7`. Only `k=4,5,6` remain.

For `k=4`, primitivity leaves `(a,b)=(1,5),(3,7)`. In the first pair,
`y^5=x^4z` and `z^5=xyv^3`; in the second, `y^5=x^3zv` and `z^5=yv^4`.
Thus both pure caps are at most five. The mixed triangle has six words, and
the third relation in (S1), at `(3,1)` or `(1,3)`, removes one. Consequently
`P_C<=9+5=14`. Already `sigma_C<=k=4`, so
`beta_1<=14+4+1+9=28<29`.

For `k=5`, the four pairs are `(1,4),(2,5),(3,6),(4,7)`. Their short pure
relations, in that order, are

\[
z^2=xv,\qquad z^2=yv,\qquad y^2=xz,\qquad y^2=xv.
\]

The other pure cap is at most five by (S1). Thus the axes contribute at most
six words; the mixed cutoff leaves at most three mixed words because one
exponent must equal one. Hence `P_C<=9`, `sigma_C<=2`, and `beta_1<=21`.

For `k=6`, primitivity leaves `(1,3),(3,5),(5,7)`. For the two outer pairs,
(S1) gives pure caps at most `3,7` in one order. The axes contribute at most
nine words. The mixed triangle contains at most `3+2=5` words when one
exponent is at most two. Thus `P_C<=14`, `sigma_C<=3`, and `beta_1<=27`.
For the middle pair, `yz=xv`, so `P_C<=9`, `sigma_C<=2`, and `beta_1<=21`.
Every case is below `L_1(8)=29`.

These are small integer gap classifications, with each exceptional class
proved by displayed endpoint relations. They do not require exact invariant
tables or a table of maxima.

## 5. Lower widths and a rejected conjecture

The known `u=3` identity and `(u,a,b)=(4,1,3)` boundary patch remain necessary
because the universal endpoint bound itself exceeds `L_1(u)` there. For the
other width-four pairs `(1,2),(2,3)`, both `y^2` and `z^2` vanish in `Q_C`.
Thus `D` lies in a two-by-two square. If `P_C=4` its socle has dimension one;
if `P_C<=3` its socle has dimension at most two. In either event
`P_C+sigma_C<=5`. As `R=0`, this gives `beta_1<=6<L_1(4)=7`.

The proposed stronger global inequality

\[
P_C\le\max\{2u-3,\lfloor(u+1)^2/8\rfloor\}
\]

is false. For `(u,a,b)=(10,1,6)`, direct exact homogeneous fibers give
`P_C=18`, whereas the proposed right side is `17`. For `(12,1,7)`, the values
are `25` and `21`. Neither inequality is used above.

## 6. Verification and scope

`small_width/verify_structural_bounds.py` independently constructs exact
homogeneous fibers, checks the new containment and counting bounds against
every primitive oriented pair for `3<=u<=20`, checks all displayed small-case
relations, and verifies the polynomial identities (S6). It also checks the
196 historical rows against these independent fibers. The paper proof does
not infer its universal quantifiers from those checks.

Every first-row assertion is uniform in all `m,d` satisfying (N1): only the
already proved endpoint inequalities for the original orientation are used.
No reflection is applied to `H_x` or `R`, and no value of `m` or `d` is sampled.
The higher rows and the existing boundary patch are unchanged.
