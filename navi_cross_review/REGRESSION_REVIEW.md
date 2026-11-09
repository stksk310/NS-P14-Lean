# Independent finite regression review of the Navi proposal

Reviewed on 2026-11-09. All reported numerical claims checked below agree with
an independent implementation. This report supplies exact finite regression
evidence; it is not a proof of an inequality for every multiplicity.

## Definitions and scope

Use the frozen manuscript's section 15 and O10 with `rho=m-1`. Write

\[
B_i(e,m)=\sum_{j=1}^{e}\binom{j-1}{i-1}T_j(e,m),\qquad
\Delta f(e,m)=f(e,m+1)-f(e,m),\qquad
F_i(m)=i\binom m{i+1}.
\]

Thus `rho` also changes from `m-1` to `m` in each multiplicity increment.
The sweep below uses exactly this convention. The `B_i` are the maximal
first-hit **lex upper bounds** in O9/O13; they are not asserted to be the
actual Betti numbers of any given numerical-semigroup tangent cone.

The `T_j` have a more specific interpretation. For each of the 83 checked
maximal-first-hit profiles, they are exactly the numbers of minimal generators
of largest variable `j` of the auxiliary lex ideal. They are not generator
counts of the actual tangent-cone defining ideal. The checker verifies this
interpretation by constructing only the small standard prefixes, checking
their downward closure, and directly testing all immediate divisors of each
candidate minimal generator. It also independently sums the degreewise O7
counts. Both computations match O10 in all 83 cases. Beyond degree `m-1` the
standard prefix is precisely
`X_(e-1)^a X_e^(d-a)`, `0 <= a < m`; there are no generators after degree `m`.

## Independent calculation

The standalone checker is
[`checks/check_navi_regression.py`](checks/check_navi_regression.py), with saved
output [`checks/REGRESSION_RESULTS.json`](checks/REGRESSION_RESULTS.json).

It does not import or execute the frozen checker. It finds the last monomial
of a lex prefix by binary search among binomial-sized exponent blocks. The
number of complete blocks before first exponent `a` is

\[
\binom{v+d-1}{d}-\binom{v+d-a-1}{d-a}.
\]

The same block decomposition, with the allowed variable count in place of
`v`, gives all support counts `S_j` without enumerating a complete degree
layer. The rank/support primitives agree with exhaustive enumeration of all
451 nonempty prefixes for `2 <= e <= 5`, `1 <= d <= 5`. Full degree layers
are enumerated only in these tiny primitive checks. The 83 direct generator
audits enumerate at most 53 standard monomials in any degree.

Reproduce from the repository root:

```sh
python3 -B navi_cross_review/checks/check_navi_regression.py \
  --max-m 200 --out navi_cross_review/checks/REGRESSION_RESULTS.json
```

The complete run took approximately 2.8 seconds in this workspace. All 24 files
listed in the frozen `proof_integrated_v2/MANIFEST_SHA256.json` still match
their recorded hashes. The original checker and certificate were not written.

## Frozen 83-profile certificate

All 83 Hilbert sequences, largest-variable generator vectors, source vectors,
and target vectors agree exactly with the frozen certificate: **83 profiles,
665 scalar comparisons, zero shortfalls**. The canonical profile digest is

```text
e10afc786ae3d55a1d35e65533696792ebf4ff4daea18c61806594623d09c65a
```

The minimum scalar margin is **67**, achieved at both
`(e,m,i)=(5,15,1)` with `105-38`, and `(6,16,1)` with `120-53`.
The frozen certificate records the first of these tied minima.

## All rows at the five proposed bases

Vectors list rows `i=1,...,e`; each inequality was checked componentwise.

| `(e,m)` | `B_i(e,m)` | `F_i(m)` |
|---|---|---|
| `(5,15)` | `(38,122,155,90,20)` | `(105,910,4095,12012,25025)` |
| `(6,16)` | `(53,213,363,319,143,26)` | `(120,1120,5460,17472,40040,68640)` |
| `(7,17)` | `(62,298,636,747,503,183,28)` | `(136,1360,7140,24752,61880,116688,170170)` |
| `(8,18)` | `(72,402,1032,1523,1376,756,233,31)` | `(153,1632,9180,34272,92820,190944,306306,388960)` |
| `(9,19)` | `(86,549,1651,2940,3340,2461,1144,306,36)` | `(171,1938,11628,46512,135660,302328,529074,739024,831402)` |

The stated first-row source/target pairs are therefore correct:
`38/105`, `53/120`, `62/136`, `72/153`, `86/171`.
The checks cover all **35** positive base rows, including the top row.

## Multiplicity-increment regression

For every `e=5,...,9` and every integer `e+10 <= m <= 200`, the independent
checker evaluated O10 separately at `m` and `m+1`. This gives **920 increments**
and **6,430 largest-variable slot comparisons**. Every instance satisfies

\[
\Delta T_j\ge0,\qquad
\Delta B_i\le\binom{e-1}{i-1}\Delta B_1,\qquad
\Delta B_1\le m.
\]

The smallest `Delta T_j` is zero; 4,416 tested slots are zero. The largest
observed `Delta B_1` values, with the first multiplicity attaining each, are:

| `e` | largest `Delta B_1` | `m` |
|---:|---:|---:|
| 5 | 14 | 165 |
| 6 | 17 | 120 |
| 7 | 17 | 120 |
| 8 | 24 | 120 |
| 9 | 24 | 120 |

The two requested larger isolated tests also agree:

| `(e,m)` | `Delta T_1,...,Delta T_e` | `Delta B_1` |
|---|---|---:|
| `(9,1000)` | `(0,0,0,0,0,1,4,6,13)` | 24 |
| `(9,10000)` | `(0,0,0,0,0,0,0,1,18)` | 19 |

For completeness, the corresponding full `Delta B` vectors are respectively
`(24,175,560,1028,1185,879,410,110,13)` and
`(19,151,525,1043,1295,1029,511,145,18)`.
The slot positivity and both increment bounds also pass at these two points.

## What this evidence does and does not establish

The numerical proposal is consistent with every requested check. In
particular, the same auxiliary lex-generator interpretation is used at the
two ends of each increment; no actual-semigroup realization is assumed.

Universal monotonicity must account explicitly for the final slot's `-m+1`
term in O10. In the increment, its contribution `-1` cancels the newly included
degree-`m-1` support count
`S_(e-1)(m-1,m)=1`. Ignoring that term would not justify `Delta T_e >= 0`.
All remaining degreewise prefix increments are nonnegative, but the global
bound `Delta B_1 <= m` needs its own argument for arbitrary `m`.

The finite sweep and two large points cannot establish that global bound.
Likewise, replacing the existing 83-profile/tail proof requires the universal
increment lemma together with a justified comparison to target increments,
and retains the already-audited O9/O13 reduction from actual source Betti
numbers to `B_i`. This report does not treat those reductions, any numerical
sample, or the auxiliary generator interpretation as a substitute for that
universal proof.
