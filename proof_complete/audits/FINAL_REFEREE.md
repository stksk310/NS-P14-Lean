# Independent final referee report for N4

Date: 2026-11-09. Scope: every numerical semigroup with exactly four atoms,
physical width `w = g4 - m <= m - 2`, over an arbitrary field, compared
degree by degree in **total graded Betti number** with its actual interval
completion `<m,m+1,...,m+w>`. This is a mathematical audit and an independent
reproduction of finite integer computations, not Lean kernel verification.

## Verdict

**No remaining mathematical blocker was found in the five audited components.**
Together they prove the stated N4 inequality in all homological degrees,
subject to the explicitly identified published inputs below. No historical
N4 closure statement, graph-rank/TU claim, finite-m extrapolation, or
characteristic-independence assertion for the source Betti numbers is used
as evidence in this verdict.

Audited documents:

1. `n4_work/endpoint_model/ENDPOINT_FOUNDATION_AUDIT_JA.md`.
2. `n4_work/nonprimitive/NONPRIMITIVE_AUDIT_JA.md`.
3. `n4_work/higher_rows/HIGHER_ROWS_AUDIT.md`.
4. `n4_work/boundary_family/BOUNDARY_FAMILY_PROOF_JA.md`.
5. `n4_work/primitive_first/PRIMITIVE_FIRST_ROW_AUDIT_JA.md`.

The independent review included complete reading of these proofs, reading
the three finite checkers, complete read-only reproduction of the first-row
finite values, a fresh higher-row certificate run, a fresh boundary checker
run, and supplementary threshold checks. The qualifications are stated
explicitly in the final section.

## 1. Quantifiers and exhaustive branch split

Write the four atoms as

`m, m+A, m+B, m+w`, with `0<A<B<w<=m-2`.

Let `d=gcd(A,B,w)`, and write `A=da, B=db, w=du`. Then
`0<a<b<u`, `gcd(a,b,u)=1`, and the numerical-semigroup hypothesis gives
`gcd(m,d)=1`. This splits every input into exactly one of:

* `d=1`: primitive physical width `w=u`;
* `d>=2`: nonprimitive physical width `w=du`.

All source and target generators lie in `[m,2m-2]`, so all displayed
generators are atoms. The comparison is between the source's minimal
four-variable presentation and the target's minimal `(w+1)`-variable
presentation. It is not a comparison with an ordinary semigroup or with
an interval of compressed width `u`.

For primitive width `w=3`, the sole pair is `(a,b)=(1,2)` and source equals
target. For larger primitive widths, first row and higher rows are treated
separately. The first-row finite exceptions are precisely
`(a,b,w)=(1,w-1,w)`, `3<=w<=10`; width 3 is equality, and the seven remaining
widths are covered for all `m>=w+2` by the boundary proof. Thus the fact
that the general first-row estimate is stated for `m>w`, while that patch
is proved for `m>=w+2`, leaves no input in the requested N4 domain uncovered.

## 2. Endpoint foundation: hard steps checked

The graded map from the homogeneous offset core to the actual tangent cone
is a surjection and has a monomial kernel **in the core's `(degree,offset)`
basis**. In fixed degree, different offsets yield different numerical
weights; a fiber is killed exactly when its weight has a longer
factorization. This justifies the kernel assertion in every characteristic.
It does not assert that the defining ideal in four polynomial variables
is monomial.

The endpoint coordinates are nonnegative and unique, the prefix argument
reduces internal words to length at most `u-1`, and all residue ideals are
nonzero under `gcd(a,b,u)=1`. The residue decomposition is used only as an
`E=k[x,v]`-module decomposition, not incorrectly as an `S`-module or a free
decomposition.

The equality of numerical weights forces a longer factorization's length
increment to be `jd`, not `j`, because `gcd(m,d)=1`. The resulting clamp
formula is exact after retaining `N_s=M_s intersect T_s`. Its use does not
discard the condition that the shorter source point actually belongs to
the core. The periodic finite cutoff is proved after the first coordinate
has become zero; it is not inferred from sampled competition depths.

The socle injection
`M_s/(M_s intersect T_s) -> E/T_s` is valid. The staircase counting argument
explicitly proves that `T_s` contains a pure `v` power before using its
first endpoint coordinate zero. The bound `R<=W-u` is correct, as is the
additional bound from `H_x`. The stronger and unjustified statement
`P_C+R<=W` is not used.

The `E`-rank-zero assertion follows from `v^m=0`; finite generation follows
from the core construction. Thus endpoint Koszul homology dimensions are
`(P,P+R,R)`. The two-variable Artin quotient and its socle are genuinely
finite monomial-basis computations. The quotient comparison in Section 8
uses the actual kernel and the Tor exact sequence; no false Betti
monotonicity for arbitrary quotients is assumed.

The bounded first-quadrant endpoint/internal Koszul spectral sequence
does give the asserted upper bounds. Its relevant endpoint homology is
finite dimensional. Later pages can only decrease dimensions in each
total homological degree. Treating the two upper rows by chain dimensions
does not set any transferred differential equal to zero.

## 3. Nonprimitive proof

The elementary shortened-word argument is valid. For a zero-free mixed
word of length `u-1`, swapping distinct adjacent letters changes exactly
one of the `u` distinct prefix residues, so it must collide with one of
the other `u-1` residues. This contradicts zero-freeness of the multiset.
For pure words the stated endpoint substitution exists; the integer carry
is nonnegative because a positive integer congruent to an offset in
`(0,u)` cannot be a smaller positive representative differing by `u`.
These arguments prove internal length at most `u-2` without importing a
historical shortening theorem.

The actual `Q=G/(x,v)G` is a monomial Artin quotient of `k[y,z]`: distinct
pure internal exponent pairs cannot have both equal degree and equal
offset. The bounds on `P`, its internal socle, and the common endpoint
socle follow. The latter uses an actual submodule injection and permits
non-Artinian ambient endpoint quotients.

The final polynomial comparisons use physical target width `V=du>=2u`.
They are positive for every integer `u>=3`, including the smallest case.
Rows beyond four vanish for the source. Consequently this branch requires
no finite campaign and pays all rows for every admissible `m,d,k`.

## 4. Primitive first row

The chosen monomial order is global. For a minimal core leading monomial,
the standard binomial partner is relatively prime to it. The weight and
average-offset arguments really exclude a `v` factor and an `xy` factor,
leaving the claimed two support faces `k[y,z] union k[x,z]`.
The pure power caps have the correct leading orientation, including the
equal-internal-weight lexicographic case.

The identification of the internal standard set `D` with the endpoint
quotient's basis is valid: an endpoint representation with positive `v`
has smaller first weight, and a representation with positive `x` but no
`v` has smaller `y` exponent in the lexicographic comparison. The mixed
degree estimate applies Savchev--Chen to a genuinely zero-free sequence.
After the unit transformation its two distinct values must include 1;
the replacement `Y_alpha^c=x^(c-1-k)Y_beta v^k` has nonnegative exponents
and positive total endpoint degree. The subsequent integer inequality
does imply `s+t<=floor(w/2)`.

For a noncore minimal forbidden monomial, **every** longer representation
is relatively prime to it, by dividing any common variable. This is the
correct strong form needed in the five-support argument. The five classes
are exhaustive: no-`x`, `xz`, `xv`, `xyv`, and `xzv`. In particular both
three-variable classes are retained. In those classes the assignment to
`(r,length increment)` is injective because the pure cap is at most the
correct congruence period `w/gcd(a,w)` or `w/gcd(b,w)`. No invertibility of
an arbitrary offset modulo `w` is assumed.

The all-m bound `beta_1(G)<=U(a,b,w)` is therefore established before the
finite enumeration begins. The estimate for `w>=48` has the stated
positive polynomial difference. The direct-fiber checker correctly
constructs the core leading ideal from shortest offset lengths: for
`x^X z^t`, a no-`v` alternative with positive `y` is lexicographically
larger, so only a positive-`v` alternative can produce its leading
membership. The pure caps give a rigorous finite box for all candidates.

I recomputed all 13,921 rows using `calculate()` in a read-only invocation,
independently enumerated the parameter range, normalized the tuple/list
representation, and obtained exact agreement with every certificate row.
The only negative-slack cases were the eight stated boundary offsets.
I also recomputed and confirmed the canonical payload hash:

`43d50ab43a88bee6648312b10e7a8c539edce06ccf938768ba64fa26bcdaf0ef`.

## 5. Primitive higher rows

The shortened internal-word bound, `P`, internal socle, and endpoint socle
bounds were independently checked as in the nonprimitive argument.
The target lower bounds include the necessary correction terms: in
particular `F2>=2*binom(w,3)+w`, not just the leading determinantal term.
The symbolic polynomial payments cover row 2 for `w>=11` and rows 3,4 for
`w>=5`; the smaller cases are handled explicitly.

For `m>=w(w-2)`, competition thresholds have zero `x` exponent and `v`
exponent at least `w-2`, while minimal core points have `v` exponent at
most `w-3`. This really gives `R=0` and equality of the actual endpoint
quotient with the homogeneous core endpoint quotient as an internal
algebra. Thus both `P` and its socle are constant throughout the entire
infinite tail. Comparing with the target's minimum over all residues of
`m` pays all tail multiplicities.

The alternative actual-order finite cutoff is also sound. Lexicographic
Dijkstra gives the least offset in each class modulo `m` and its least
word length. Above `b_rho+m*ell_rho`, the maximum order is exactly
`(N-b_rho)/m`. Hence every common endpoint-socle basis weight lies below
the finite maximum threshold. The checker scans all such weights, and
the internal quotient test uses the actual maximum orders. The proof that
individual multiplication maps have injective nonzero basis images makes
these kernel counts valid in all characteristics.

A fresh full run, writing only `/tmp/n4_referee_higher_rows.json`, returned
PASS with 4,824 finite points, of which 4,716 are true narrow, and 108
infinite tails. The payload hash was independently recomputed and equals

`44dae4892039cec415b1edcfba6367d97d655e37f3ae559ad1f5e3842b9c16e5`.

The maxima of `2P+3R+sigma` by widths 4 through 10 are
`12,16,20,24,30,35,41`, against target minima
`12,25,46,77,120,177,250`. The finite domain and the stable tail are
exhaustive, so this is a finite computational proof, not a grid-based
inference about an unbounded multiplicity.

## 6. Boundary-family patch

The explicitly listed core standard columns are independent in
`(degree,offset)`, so the claimed core Groebner basis does not rest merely
on a numerical Hilbert-series comparison. At a fixed competitor residue,
the free anchor and the stated single restricted anchor exhaust all
standard columns. Their threshold inequalities are necessary and
sufficient, and restricted-anchor cap overflow is already covered by the
free anchor. The resulting monomial ideal is the actual initial ideal
of the actual tangent-cone ideal.

The filtration is by columns in decreasing internal weight; multiplication
by either internal variable strictly raises that weight or becomes zero.
Its factors have the stated endpoint quotient form. The two-variable
corner resolutions tensor with the internal Koszul complex in every
characteristic. Empty factors are assigned nonnegative budgets, so the
negative constants in the displayed formulas are never incorrectly
subtracted for an empty column.

For width 4, the colon calculation is correct and the mapping-cone map
can be chosen with every entry divisible by the independent variable `x`.
This proves minimality and the stated Betti table in all characteristics.
The width-5 generator count and Euler bound suffice. For widths 6 through
10, the four residue branches in the positive-threshold count cover all
possibilities and impose the restricted-column cap. Summing their bounds
gives the claimed finite budgets and the displayed comparisons.

As a supplementary check, I independently evaluated the number of
positive thresholds smaller than the existing cap for 172,548 triples
`(t,m,j)`, with `3<=t<=29` and a range extending beyond the necessary
competition thresholds. Every count was at most `max(t-2j-2,0)`.
This check is not substituted for the residue-branch proof.

A fresh boundary checker run returned PASS: 231 actual-order regressions,
16 optional Taylor cases, 10 lcm classes. Its reported certificate hash is

`e6bb1ea1975d83a67e19dbf367d911c025175a99c5190a806d5b75bf4137d178`.

The optional Taylor argument also uses legitimate unit pivots and zero
residuals, so it is universal in the characteristic. The main boundary
proof needs none of those finite rank computations.

### 6.1 Independently checked shorter patch needed for the final N4 assembly

The parent proposed removing the boundary family's higher-row proof from
the necessary dependency graph, because the general primitive higher-row
proof already handles these offsets. I independently verified the
following first-row-only replacement in full.

For `(a,b,w)=(1,w-1,w)`, reducing the displayed core Groebner basis modulo
`(x,v)` gives

`Q_C = k[y,z]/(yz,y^(w-1),z^(w-1))`.

Thus `P_C=2w-3` and `sigma=2`. The directed Cayley graph has steps `+1`
and `-1`, so its shortest internal word lengths are
`ell_r=min(r,w-r)`. Summing the two symmetric halves gives

`W=1+sum_r ell_r = 1+floor(w^2/4)`.

The endpoint foundation, applied directly to this actual source, gives
`R<=W-w` and therefore

`beta_1(G)<=P_C+sigma+1+R = 2w+R <= W+w`.

For `w>=6`, this is at most `binom(w,2)+1`. Explicitly, if `w=2h`,
the needed inequality is `h^2<=h(2h-3)`, valid for `h>=3`. If
`w=2h+1>=7`, it is `h(h+1)<=(2h+1)(h-1)`, equivalent to
`h^2-2h-1>=0`, valid for `h>=3`. Hence this covers every boundary
width at least 6, with no threshold-counting lemma or higher-row boundary
resolution.

At width 4 and `m>6`, the explicit monomial ideal itself has minimal
generator counts `(6,8,8,6)` in residue classes `m mod 4=(0,1,2,3)`.
The corresponding actual target first Betti numbers are `(7,10,9,8)`.
For `m=6`, the displayed six-generator ideal gives `6<=9` directly.
These statements need only minimal monomial generator counts; the
mapping-cone calculation is unnecessary. At width 5 the already proved
generator bound `mu(J)<=10` is less than the minimum target first Betti
number 11. Width 3 remains source=target.

Consequently this shorter patch is sufficient for the final N4 assembly
and is independently accepted by this referee. The full boundary proof
above remains a valid stronger attached result, but its mapping cone,
positive-threshold budgets, and optional Taylor calculations need not
occur among the necessary ancestors of N4.

## 7. What the verdict does and does not certify

The only specialized published mathematical inputs remaining in the
assembled N4 proof are:

* Savchev--Chen's long zero-free sequence theorem, used for the primitive
  first-row mixed-word estimate.
* The arbitrary-field arithmetic-sequence Betti formula of
  Gimenez--Sengupta--Srinivasan and the equality with tangent-cone Betti
  numbers in Herzog--Stamate Proposition 2.5, used for target higher rows.
  The primitive first row independently derives its own target capacity.

The parent independently checked these primary statements and the target
residue conversion. This referee report has audited their mathematical
applications; it does not claim an additional independent retrieval of
those external primary texts or a new proof of those published theorems.
All other invoked facts are the explicitly applied standard algebraic
tools: Koszul homology, finite free-resolution Euler characteristic,
Tor long exact sequences, bounded spectral sequences, monomial corner
resolutions, Groebner degeneration, and the explicit minimal mapping cone.

The finite first-row and small-width second-row portions remain exact
Python integer computations with a proved exhaustive finite reduction.
They are independently reproducible and were reproduced in this audit.
They have not been checked by the Lean kernel. Source total Betti numbers
need not themselves be characteristic independent: each bound is proved
over an arbitrary fixed field, with the combinatorial right-hand side
independent of that field.

With these qualifications stated, the union of the five components
covers all admissible four-atom inputs, all multiplicities in the requested
true-narrow range, all fields, and all homological degrees. There is no
remaining open rank condition or unbounded numerical search in N4.

## 8. 統合稿点検

対象：`proof_complete/NS_P14_COMPLETE_PROOF_JA.md`、全3501行。
2026-11-09、単独監査稿から統合稿への論理的組立てを追加で独立点検した。
**指定された組立て箇所に、新たな欠落・循環依存・対象の取り違えは認めなかった。**

### 8.1 N4の量化と分割

12.1では元の四つのactual atomから
`d=gcd(g2-m,g3-m,g4-m)`、`w=du` を取り、
`gcd(m,d)=1` は元の数値半群性、`gcd(a,b,u)=1` は正規化から従う。
`du<=m-2` なので共通基礎の `m>u` と各枝の狭幅条件を満たす。
比較先を圧縮幅 `u` の区間に置き換えず、非primitive枝では物理幅 `du`
を保持している。primitive枝だけで `u=w` と書き直すことに矛盾はない。
12.7は全枝、全第一行例外、width 3の同一source/targetを正しく合成する。

### 8.2 旧合同候補リスト削除と有限DP完全性

12.5から旧3.1の合同候補リストを削除しても、現在の有限DP完全性証明は
独立に成立する。必要な論理は次だけである。

1. (C1)の二面支持が全最小生成元の支持を尽くす。
2. (C3)のpure capにより、`yz`面では `0<=s<=p,0<=t<=q`、
   正`x`面では `1<=t<q0<=q` に全最小生成元が入る。
3. (F4)は内部面のmembershipを、(F5)は各正`x`列の最初のmembershipを、
   それぞれ最短offset長から必要十分に判定する。
4. 可除候補を除くと正確に全最小生成元となり、参照offsetは
   `ap+bq` 以下である。

この4段階は削除された合同候補の包含・逆包含を一切引用しない。
13,921件の有限評価の意味も変化しない。統合先のchecker二本は既監査版と
`diff`で完全一致し、統合先の二つの圧縮証書のcanonical payload hashも
それぞれ本報告の既確認値と一致した。

### 8.3 first-only例外証明

12.6 B2--B3の実initial idealの同定から、幅4の最小生成元計数と幅5の
10本上界だけを第一行に使う構成は正しい。幅4の `m=6` は別処理され、
`m>6` は四つの剰余が全multiplicityを覆う。
幅6以上は本報告6.1の独立検証と同じ
`Q_C=k[y,z]/(yz,y^(w-1),z^(w-1))`、`W=1+floor(w^2/4)`、
`beta1<=W+w` の短い証明で閉じる。偶数・奇数の差の表示も正しい。
高次行は12.4が既に全primitive offsetを覆うので、mapping cone、
境界高次行の閾値予算、Taylor rankを省いたことに未充足の行はない。

### 8.4 付録A、C、Dの接続

付録Aの入力 `e>=5,u<m` は、13の狭幅枝で元のatomを正規化すると
必ず満たされる。内部offsetが相異なるため `u>=e-1` でもある。
付録Aの幅の範囲は隙間なく接続する：
`e>=8` は密な `u<=2e-3` と疎な `u>=2e-2`、
`e=6` は `u<=9` と `u>=10`、`e=7` は `u<=11` と `u>=12`、
`e=5` は `u=4,5,6,7` と `u>=8` である。

A1が参照するC2--C4は一般内部変数数のactual endpoint構成であり、
第12節F4--F6の二変数平面corner論法は内部変数数に依存しない。
ここで必要なのは `m>u` で、`du<m` は不要であることもC側で明記され、
両側の仮定は一致している。C1の実効幅
`V=min(du,m-1)>=u` と容量の単調性はactual targetを保持する。

A2の `t=0` は完全算術列であり、C6または同じ公刊算術列公式で処理できる。
`t=1` は `u=e=q+2` の一欠落族なので、付録Dの入力に正確に一致する。
内部欠落では `r',s>=1`、`r'+s=q>=3` でD4の二包含単射の条件を満たす。
端欠落ではD5が必要な第 `q+1` 行の指示項を保持している。
付録DはC1--C4のみを使い、付録Aの結論を前提にしないため循環はない。
またC6の最小幅処理は算術列公式から直接導かれ、Aへの循環を作らない。

### 8.5 第13節の全場合

物理幅は整数なので `w<=m-2` と `w>=m-1` は全域の排他的分割である。
前者は `e>=5` の付録A、`e=4` のN4、`e=3` の明示した公刊定理、
`e<=2` の直接計算で尽くされる。

後者のcompletionのactual atomは正確に `m,...,2m-1`。
第4節のcutには `r<=e-1` があるため、`r>=4` の残余は必ず `e>=5`。
その場合 `delta>=a>=binom(r+1,2)>=10` なので、
`e>=10` は第10--11節の入力、`5<=e<=9` は付録Bの
`m>=e+10` という入力に一致する。`r=2,3` は第9節が全deltaを処理する。
従ってwide側に小生成元数や小deltaの未処理範囲はない。
`e=1,2` の最後の直接計算は幅の大小によらず適用できる。
有限体への同標数純超越拡大とBetti数の体拡大不変性も、結論の任意体性を
正しく元の体へ戻す。

この追記は統合時の依存関係と指定された接続箇所の追加監査であり、
本報告が元来担当していないordinary共通鎖・幅側内部の全補題について、
今回新たに独立再証明したという意味にはしない。既監査部分をそのまま
入力とした最終組立てには、N4の未証明境界が再導入されていない。
