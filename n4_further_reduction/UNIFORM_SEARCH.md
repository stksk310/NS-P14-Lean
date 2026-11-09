# N4: a proved structural reduction from 196 offset rows to 46

This note supplements, and does not edit, `proof_integrated_v2/NS_P14_INTEGRATED_PROOF_JA.md` §§12 and 14. The inequalities below apply to every allowed actual source multiplicity and dilation; they do not rely on finite samples of either parameter. The old 196-row certificate is used only for regression checks.

The proved result is that the first-row comparison closes uniformly at `u=5` and every `u>=9`. Thus the existing finite offset audit can be restricted to `u in {3,4,6,7,8}`, comprising **46 ordered-orientation offset pairs**, rather than 196. The old exceptional treatments at `(u,a,b)=(3,1,2)` and `(4,1,3)` remain in place. No source Betti reflection or Cohen–Macaulay hypothesis is used.

## 1. Three endpoint relations improve the standard-word count

Keep the notation of §14: `0<a<b<u`, `h=floor(u/2)`, and the divisor-closed standard-word set `D`. The existing mixed-word theorem gives

\[
(s,t)\in D,\quad st>0\quad\Longrightarrow\quad s+t\le h.
\]

There are three elementary homogeneous relations in the core:

\[
 y^b=x^{b-a}z^a,\qquad
 z^{u-a}=y^{u-b}v^{b-a},\qquad
 y^{u-b}z^a=x^{u-b}v^a.
\tag{U1}
\]

Each right-hand side contains an endpoint. Therefore no standard word is divisible by any of `y^b`, `z^(u-a)`, or `y^(u-b)z^a`.

Set `p=u-b`, `q=a`, `k=p+q=u-(b-a)`. Both `p,q>=1`, hence `k>=2`. The two pure axes, including the unit only once, contribute at most

\[
 (b-1)+(u-a-1)+1=2u-k-1
\]

points. The mixed triangle has `binom(h,2)` points. If `k<=h`, its points with `s>=p,t>=q` number exactly `binom(h-k+2,2)` and are forbidden by the third relation. Consequently

\[
 P_C\le 2u-k-1+\binom h2-Q_h(k),\qquad
 Q_h(k)=\begin{cases}\binom{h-k+2}{2}&k\le h,\\0&k>h.\end{cases}
\tag{U2}
\]

For `k>=h+1`, `k+Q_h(k)>=h+1` immediately. For `k<=h`, put `r=h-k>=0`; then

\[
 k+Q_h(k)=h-r+\binom{r+2}{2}
 =h+1+\frac{r(r+1)}2\ge h+1.
\]

Thus, for every width and every offset pair,

\[
\boxed{P_C\le B_{\rm new}(u):=2u-h-2+\binom h2.}
\tag{U3}
\]

This improves the old `binom(h,2)+2u-3` by `h-1`, using only three displayed endpoint relations and the already proved mixed-word theorem. Further gcd reductions of the relations are unnecessary for this conclusion.

## 2. The same forbidden rectangle bounds the socle

Every mixed socle point has `1<=s<=h-1`; an antichain has at most one point at each first coordinate, so there are at most `h-1` mixed socle points. At most two further socle points lie on the axes. Hence

\[
\boxed{\sigma_C\le h+1.}
\tag{U4}
\]

There is also a useful coupled version. A mixed point avoids `s>=p,t>=q`. Partition mixed socle points into those with `s<p` and the rest. The first group has at most `p-1` points because first coordinates in an antichain are distinct. Every point in the second group has `t<q`, so that group has at most `q-1` points because second coordinates are distinct. Including the two possible axis points gives

\[
\boxed{\sigma_C\le\min(h+1,k).}
\tag{U5}
\]

The uniform tail below needs only (U4); (U5) is a proved additional bound, not an empirical guess.

## 3. The new infinite-width threshold is 9

From the existing actual-kernel endpoint estimate, valid for all `m,d`,

\[
\beta_1(G)\le P_C+\sigma_C+1+R,\qquad
R\le W-u\le1+\left\lfloor\frac{u^2}{4}\right\rfloor-u.
\]

Combining (U3) and (U4), and subtracting from `L_1(u)=binom(u,2)+1`, gives the exact gaps

\[
L_1(u)-\left(B_{\rm new}(u)+(h+1)+1+1+\lfloor u^2/4\rfloor-u\right)
=\begin{cases}
 h(h-5)/2,&u=2h,\\
 (h^2-3h-2)/2,&u=2h+1.
\end{cases}
\tag{U6}
\]

The even gap is nonnegative for `h>=5`, hence `u>=10`. For odd widths put `h=4+z`, `z>=0`; the odd gap is

\[
1+\frac{z(z+5)}2\ge1,
\]

hence every odd `u>=9` closes. Since the physical width is `V=du>=u`, the already proved monotonic comparison `F_1(m,V)>=L_1(V)>=L_1(u)` completes the first row for **all `u>=9` and every allowed `m,d`**.

At `u=5`, (U3) gives `P_C<=7` and (U4) gives `sigma_C<=3`. The existing height bound `H_x<=u-3=2` forces `R=0`, so

\[
\beta_1(G)\le7+3+1=11=L_1(5).
\tag{U7}
\]

This also removes all six width-5 rows without computing any individual core.

The remaining old certificate rows have counts

| Width | Remaining pairs |
|---:|---:|
|3|1|
|4|3|
|6|9|
|7|15|
|8|18|
|Total|46|

The existing high-row argument and the two exceptional source families are unaffected. The claim is a reduction in required offset rows, not a claim that all residual rows are genuinely necessary.

## 4. Verification and limits

Run

```sh
python n4_further_reduction/uniform/check_uniform_reduction.py
```

The script cross-checks (U2), (U3), and (U5) against all 196 old exact core rows, verifies the displayed elementary integer identities, and confirms that 150 rows are removed and 46 remain. It enumerates **zero multiplicities and zero dilations**. The universal mathematical proof is the argument above; the finite loop checking the algebra is only a regression check.

This bounded search stopped after the two proved structural lemmas (standard-word count and socle antichain). No claim that 46 is minimal has been proved. In particular, further tightening of the remaining widths may still be possible. No inequality `P_C+R<=W`, no reflection invariance of actual source Betti numbers, and no extrapolation from finite source examples is used.
