# Fresh referee report on the universal Navi increment bound

2026-11-09. Reviewed independently against V02 section 15, especially
(O6), (O8)–(O10), (O13), and the completed
`INCREMENT_LEMMA_AUDIT.md`. No existing proof or certificate was edited.

**Verdict: the universal increment proof is correct.** There is no missing
finite bridge. For `5 <= e <= 9, m >= e+10`, it proves

\[
0\le\Delta T_j,\qquad
0\le\Delta B_1\le m-1<m.
\]

The five stated first-row bases suffice for all rows, with the nonnegative
slot and normalized-target arguments given below. The resulting replacement
removes the 83-profile comparison and the five tail estimates, while retaining
the actual-to-formal reductions (O9), (O13). This conclusion does not require
the formal profile to be realized by an actual semigroup.

## 1. Endpoint cancellation and the exact quantity being bounded

Here `Delta` means `f(e,m+1)-f(e,m)` with `e` fixed. In particular the
maximal first-hit changes from `rho=m-1` to `rho=m`. Define `T_j` by the
right sides of (O10), and

\[
B_i(e,m)=\sum_{j=1}^e\binom{j-1}{i-1}T_j(e,m).
\]

When (O10) is differenced, its newly present degree is `m-1`, with cap
`min(m,N_(m-1))=m`. The first `m` words of that degree are exactly

\[
X_e^{m-1},\ X_{e-1}X_e^{m-2},\ldots,X_{e-1}^{m-1}.
\]

Thus `S_(j-1)(m-1,m)=0` for `j<e`, and it is 1 for `j=e`.
The latter cancels precisely the change `-1` in `e-m+1`. There is no
remaining terminal term. For every slot,

\[
\Delta T_j=
\sum_{d=2}^{m-2}\bigl[
S_{j-1}(d,\min(m,N_d))-
S_{j-1}(d,\min(m-1,N_d))\bigr]\ge0.\tag{R1}
\]

For `N_d<m` this difference is zero. For `N_d>=m`, let `v_(d,m)` be
the `m`-th lex-smallest degree-`d` word, and let
`k_d=e-maxvar(v_(d,m))`; set `k_d=0` in the ineligible case. The summand
in (R1) is exactly `[maxvar(v_(d,m))<=j-1]`. Consequently

\[
\Delta B_1=\sum_{d=2}^{m-2}k_d
=\sum_{r=1}^{e-1}\#\{d\in[2,m-2]:k_d\ge r\}.\tag{R2}
\]

The last equality is ordinary counting by positive integer levels. It uses
`e-maxvar`, with no shift by one. In particular a word containing `X_e`
contributes zero.

## 2. Both rank bounds, including the first-layer improvement, are valid

Among all degree-`d` words omitting `X_e`, the first is `X_(e-1)^d`,
of rank `d+1`. The second is `X_(e-2) X_(e-1)^(d-1)`, of rank
`(d+1)+d=2d+1`: the complete block on the final two variables has size
`d+1`, and the next block contains `d` words before its `X_e`-free last
word. Earlier variables cannot produce an intervening lex-smaller word.
Because the degrees in (R2) satisfy `d<=m-2`, the first `X_e`-free word
cannot have rank `m`. Therefore

\[
k_d\ge1\implies m\ge2d+1,
\qquad
\#\{d:k_d\ge1\}\le
\left\lfloor\frac{m-1}{2}\right\rfloor-1.\tag{R3}
\]

For `2<=r<=e-1`, the smallest word omitting the last `r` variables is
`X_(e-r)^d`. All words up to it are exactly the degree-`d` words on
the final `r+1` variables, so its rank is `C(d+r,r)`. Hence

\[
k_d\ge r\implies\binom{d+r}{r}\le m.\tag{R4}
\]

The inequality remains correct when equality holds and when `N_d=m`.
Only necessary conditions are used, so the overcount of eligible degrees
introduces no reverse implication.

## 3. The convex estimate and all seven rational terms check

Put `A_r=C(r+2,2)` and `C_r=C(r+2,3)`. For `d>=2`, Pascal gives

\[
\binom{d+r}{r}\ge A_r+(d-2)C_r.
\]

Indeed the first forward difference, from `d=2` to `d=3`, equals `C_r`,
and subsequent differences increase. With
`D_r=max{d>=0:C(d+r,r)<=m}`, (R4) therefore bounds the layer size by

\[
\max(D_r-1,0)\le\frac{m+C_r-A_r}{C_r}.\tag{R5}
\]

The case `D_r<2` must be checked separately. It is valid: for `r=2`
the right numerator is `m-2`, for `r=3` it is `m`, and for `r>=4`
it is positive already at `m=0`. Thus every term introduced by extending
the layer sum to `r=8` is nonnegative for `m>=2`.

The seven `(A_r,C_r)` pairs in the audited proof are correct. Independent
exact rational arithmetic gives

\[
\sum_{r=2}^8\frac1{C_r}=\frac7{15},\qquad
\sum_{r=2}^8\frac{C_r-A_r}{C_r}=\frac{517}{280}.
\]

Because `e-1<=8`, (R2), (R3), (R5) imply

\[
\Delta B_1\le\frac{m-3}{2}+\frac{7m}{15}+\frac{517}{280}
=\frac{29m}{30}+\frac{97}{280}<m
\quad(m\ge11).
\]

At `m=11` the final strict gap is exactly `17/840`; it increases
thereafter. Integrality gives `Delta B_1<=m-1`. The required domain has
`m>=15`, so no omitted small multiplicities remain. The written scope
restriction `e<=9` is necessary for this particular seven-term estimate.

## 4. Five first-row bases and all-row induction

Every slot is nonnegative, including the exceptional last one. In fact
each degree `2<=d<=m-2` contributes at least `X_(e-1)^d` to
`S_(e-1)(d,min(m-1,N_d))`, because its rank is `d+1<=m-1`. Thus

\[
T_e\ge e-m+1+(m-3)=e-2\ge0.
\]

Consequently both values and differences have the weight bounds

\[
B_i\le\binom{e-1}{i-1}B_1,
\qquad
\Delta B_i\le\binom{e-1}{i-1}\Delta B_1.
\]

For `F_i(m)=i C(m,i+1)` and `m>=e`, Pascal and binomial monotonicity give

\[
m\binom{e-1}{i-1}\le m\binom{m-1}{i-1}
=i\binom mi=\Delta F_i(m).
\]

To obtain all base rows from the first one, put
`Q_i=F_i(m)/C(e-1,i-1)`, for `1<=i<=e`. For `1<=i<e`, direct division yields

\[
\frac{Q_{i+1}}{Q_i}=
\frac{(i+1)(m-i-1)}{(i+2)(e-i)},
\]

whose numerator minus denominator is `(i+1)(m-e)-e-1`.
At `m=e+10`, this is at least `20-e-1>=10`. Thus `Q_i>=Q_1=F_1`,
and a first-row base implies every positive base row. Independent direct
enumeration reproduces the five base comparisons:

| `e` | `m` | `B_1` | `F_1` |
|---:|---:|---:|---:|
|5|15|38|105|
|6|16|53|120|
|7|17|62|136|
|8|18|72|153|
|9|19|86|171|

The increment comparison then propagates every row. The top row `i=e`
is included. For `i>e`, all EK weights and source rows vanish. Row zero
has value 1 on both sides and is handled separately.

Actual source numbers enter through the retained chain

\[
\beta_i(G)\le L_i(h,\rho)
\le L_i(\widehat h,\rho)
\le L_i(\widehat h,m-1)=B_i(e,m)\le F_i(m).
\]

The increment argument compares formal integer expressions at different
`m`; it is not an assertion about a family of actual semigroups, and does
not replace the fixed-`m` first-hit comparison (O13).

## 5. The subsequently proposed dimension-free refinement is also valid

The alternative communicated during this review admits a short independent
proof. Define

\[
K(N)=\#\{(d,r)\in\mathbb Z_{\ge2}^2:\binom{d+r}{d}\le N\}.
\]

The pairs with `min(d,r)=2` are empty for `N<6`. Otherwise let
`t=max{s>=4:C(s,2)<=N}`. They number exactly `2t-7`. For integer
`t>=4`,

\[
\binom t2-3(2t-7)=\frac{(t-6)(t-7)}2\ge0,
\]

so their count is at most `N/3`.

The pairs with `d,r>=3` are empty for `N<20`. Otherwise let
`u=max{s>=6:C(s,3)<=N}`. Binomial row monotonicity implies
`C(d+r,d)>=C(d+r,3)`, hence `d+r<=u`. There are at most
`C(u-4,2)` such ordered pairs. The exact identity

\[
\binom u3-6\binom{u-4}{2}
=\binom{u-6}{3}+3(u-6)+14\ge0\qquad(u\ge6)
\]

shows that their count is at most `N/6`. Therefore
`K(N)<=N/2`, and integrality gives `K(N)<=floor(N/2)`.
Using (R4) to overcount all layers `r>=2` by `K(m)` now yields

\[
\Delta B_1\le
\left\lfloor\frac{m-1}{2}\right\rfloor-1+
\left\lfloor\frac m2\right\rfloor
=m-2.
\]

This refinement removes the upper bound on `e` from the increment
argument itself, for the same formal O10 expressions with `e>=3,m>=5`.
It does not by itself extend the separate actual-to-formal foundations
or the five-base all-row argument to any new parameter domain.
The convex proof is already sufficient and remains correct independently.

## 6. Reproducible independent sanity evidence

`checks/check_increment_referee.py` imports no existing checker or
certificate. It generates lex words directly by increasing exponent tuples.
Running

```sh
python3 -B navi_cross_review/checks/check_increment_referee.py
```

passed exact rational arithmetic, 100 pure-word rank identities, 120 O10
endpoint/layer comparisons (`e=5,...,9`, `e+10<=m<=40`), all 35 base rows,
and 300 direct pair-count checks of the optional refinement. These finite
checks detect transcription and indexing mistakes. The universal conclusions
rest on the counting proofs above, not on the tested range.

## 7. Final Japanese synthesis: literal review and hashes

The final `NAVI_CROSS_REVIEW_JA.md` was also checked directly. Its (NI1)–(NI10)
prove the stronger `Delta B_1<=m-2`, and correctly state the original
actual-to-formal scope and the retained dependencies. In particular the
`T_e>=e-2` argument, five first-row bases, all-row base comparison, top
row, and zero conventions are consistent. No mathematical gap was found.

Two editorial domains identified during review have been resolved in that
file: (NI4) explicitly assumes `1<=r<=e-1`, and the adjacent-`Q_i` ratio
in (NI10) explicitly assumes `1<=i<e`. The later overcount by all
`r>=2` remains justified. Both the primary convex proof and the final
dimension-free proof receive a pass.

SHA-256 of the exact reviewed versions:

```text
eb3ff1c4083386a950194e4dd3b97ab95cabaa56e5119acab1d128058712bcac  INCREMENT_LEMMA_AUDIT.md
a6b4ba1fc6f6feb106af3ffbd0f3ad5f471d607329e635debdf513bbca17068f  NAVI_CROSS_REVIEW_JA.md
```
