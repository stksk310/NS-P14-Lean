# Independent audit of the full-quadratic Apéry lemma

2026-11-09. This audit concerns only the proposed feasibility lemma and its
use to exclude the three scalar corners. The integrated proof manuscript and
its certificates are not modified.

**Verdict.** The lemma is valid for every genuine numerical semigroup with its
minimal generating set and over every field. It uses the actual numerical
Apéry quotient of Section 2, not an arbitrary Artin algebra having the same
Hilbert function. The three stated corners are therefore impossible for an
actual source.

## 1. Setup and the exact role of the quotient

Let

\[
\Gamma=\langle m=g_1<g_2<\cdots<g_e\rangle,\qquad e\ge2,
\]

be a numerical semigroup with the displayed generating set minimal. For
\(v\in\Gamma\), let \(\operatorname{ord}(v)\) be the maximum number of
generators in a factorization of \(v\). It is finite because every generator
is at least \(m\). In the tangent cone \(G\), the numerical coordinate
\([v]\) has degree \(\operatorname{ord}(v)\), and

\[
[u][v]=
\begin{cases}
[u+v],&\operatorname{ord}(u+v)=\operatorname{ord}(u)+\operatorname{ord}(v),\\
0,&\operatorname{ord}(u+v)>\operatorname{ord}(u)+\operatorname{ord}(v).
\end{cases}
\]

Put \(x=[m]\), \(A=G/xG\), and let \(N\) be the span in \(A\) of its
non-Apéry numerical heads, as in Section 2. Then \(Q=A/N\) has precisely the
coordinates

\[
\{[\omega]:\omega\in\operatorname{Ap}(\Gamma,m)\}
\]

as a vector-space basis, with their original order degrees. Indeed an Apéry
coordinate has no possible predecessor \(\omega-m\in\Gamma\), so is not
in \(xG\); a non-Apéry coordinate is either in \(xG\) already or is one of
the heads subsequently killed by \(N\). This also shows the following exact
criterion for a monomial of degree two:

\[
Y_iY_j\longmapsto
\begin{cases}
[g_i+g_j],&g_i+g_j\in\operatorname{Ap}(\Gamma,m)
\text{ and }\operatorname{ord}(g_i+g_j)=2,\\
0,&\text{otherwise},
\end{cases}
\qquad(2\le i\le j\le e).                                      \tag{1}
\]

The quotient really is an algebra: whenever a product from a non-Apéry head
survives to another head, the target remains non-Apéry, since
\(v-m\in\Gamma\) implies \(v+g_i-m\in\Gamma\). Thus the indicated span
\(N\) is an ideal. Every Apéry element has a longest factorization avoiding
\(m\); that factorization gives a surviving monomial of its order degree.
Consequently the graded map

\[
\phi:k[Y_2,\ldots,Y_e]\twoheadrightarrow Q,
\qquad Y_i\mapsto[g_i],
\]

is surjective. No jump filtration, choice of linear cut, or identification
between the full torsion and head modules is needed in this argument.

## 2. Maximal quadratic dimension gives a Sidon set

Assume

\[
q_2:=\dim_kQ_2=\binom e2.
\]

The source of \(\phi_2\) has dimension
\(\binom{(e-1)+1}{2}=\binom e2\), so its surjectivity implies that
\(\phi_2\) is an isomorphism. Each quadratic monomial therefore has a
nonzero image, and distinct quadratic monomials have linearly independent
images. By (1), every \(g_i+g_j\), \(2\le i\le j\le e\), is an Apéry
element of order exactly two; these elements are pairwise distinct.

Recall that distinct Apéry elements have distinct residues modulo \(m\).
For completeness, if \(u,v\) are Apéry elements with \(u>v\) and
\(u-v=tm\), \(t\ge1\), then
\(u-m=v+(t-1)m\in\Gamma\), a contradiction.

Every non-\(m\) minimal generator \(g_i\) is an Apéry element of order
one. It cannot have \(g_i-m\in\Gamma\), because this would decompose
\(g_i\); similarly it cannot have a factorization of length at least two.
Thus \(0,g_2,\ldots,g_e\) are distinct Apéry elements with orders zero and
one, respectively. The order-two Apéry elements above cannot equal any of
these elements. By uniqueness of Apéry representatives, they also cannot
share their residues.

It follows that

\[
B=\{0,\overline{g_2},\ldots,\overline{g_e}\}
\subset\mathbb Z/m\mathbb Z
\]

has \(e\) elements and all its unordered pair sums, with repetition allowed,
are distinct. These sums are exactly the three disjoint families

\[
0+0,\qquad 0+\overline{g_i}\ (2\le i\le e),\qquad
\overline{g_i}+\overline{g_j}\ (2\le i\le j\le e).
\]

Hence \(B\) is a Sidon set in the required strong sense, including doubles.
The cross-degree exclusion in this paragraph is essential: independence of
quadratic monomials alone does not state it, but the numerical Apéry property
does prove it.

## 3. Difference injection and the multiplicity bound

Consider

\[
D:\{(b,c)\in B^2:b\ne c\}\longrightarrow
(\mathbb Z/m\mathbb Z)\setminus\{0\},\qquad D(b,c)=b-c.
\]

If \(b-c=b'-c'\), then \(b+c'=b'+c\). Sidon uniqueness gives equality
of multisets \(\{b,c'\}=\{b',c\}\). Therefore either
\(b=b'\) and \(c=c'\), or \(b=c\) and \(b'=c'\). The second
possibility is excluded by the domain of \(D\). Thus \(D\) is injective,
and counting proves

\[
\boxed{m-1\ge e(e-1),\qquad
m\ge e(e-1)+1,\qquad
\delta:=m-e\ge(e-1)^2.}                                    \tag{2}
\]

This argument also handles groups with elements of order two: such an
element cannot be a difference of distinct points of \(B\), since its
reverse ordered pair would have the same difference. No oddness assumption
on \(m\) was used.

## 4. Application to the actual-cut corners

The actual cut in Sections 4–5 is \(r=\max(2,p(q_2))\), where
\(p(a)=\max\{p:\binom{p+1}{2}\le a\}\). For \(r\ge3\), one has
\(r=p(q_2)\), and therefore

\[
\binom{r+1}{2}\le q_2\le\binom e2.
\]

If \(r=e-1\) **and \(r\ge3\)**, these two bounds coincide, so the
hypothesis of (2) follows with no additional equality assumption. Under these
two hypotheses, if also
\(\delta=\binom{r+1}{2}\), (2) requires

\[
\binom{r+1}{2}\ge r^2.
\]

This is false throughout the applicable range \(r\ge3\), because the difference is
\(r^2-\binom{r+1}{2}=r(r-1)/2>0\). The three requested exclusions are:

| \(r\) | \(e\) | Proposed \(\delta\) | Required \(\delta\ge(e-1)^2\) | Proposed \(m=e+\delta\) | Required \(m\ge e(e-1)+1\) |
|---:|---:|---:|---:|---:|---:|
| 6 | 7 | 21 | 36 | 28 | 43 |
| 7 | 8 | 28 | 49 | 36 | 57 |
| 8 | 9 | 36 | 64 | 45 | 73 |

The conclusion excludes actual numerical-semigroup sources at these corners.
It need not exclude abstract Artin algebras with the same proposed Hilbert
function; their existence would not contradict the lemma.

**Reviewed scope correction:** the actual-cut corollary excludes \(r=2\),
where the floor \(r=\max(2,p(q_2))\) does not imply
\(q_2\ge\binom{r+1}{2}=3\). For example,
\(\Gamma=\langle6,7,11\rangle\) has Apéry set
\(\{0,7,14,21,22,11\}\), hence \(q_2=2\), while
\(r=e-1=2\) and \(\delta=3\). The integrated manuscript already handles
\(r=2\) in Section 9. This scope correction leaves the universal
maximal-\(q_2\) Sidon lemma and the three \(r=6,7,8\) exclusions unchanged.

## 5. Edge cases and limitations checked

- **Arbitrary characteristic:** all arguments use a coordinate basis,
  finite-dimensional injectivity, and integer residues. If two monomials had
  the same coordinate, their difference would be a nonzero polynomial in the
  kernel even in characteristic two. No field extension is required here.
- **Embedding dimension two:** maximal \(q_2=1\) gives \(m\ge3\) and
  \(\delta\ge1\), exactly as (2) says. For example,
  \(\Gamma=\langle3,4\rangle\) has Apéry set \(\{0,4,8\}\), so
  \(q_2=1\) and equality holds. For \(\langle2,3\rangle\), \(q_2=0\),
  so there is no contradiction.
- **One-sided implication:** the proof gives a necessary condition for
  maximal \(q_2\). It does not claim that a Sidon residue set alone makes
  all quadratic products survive: their orders and Apéry minimality still
  matter.
- **Scope:** the proof is a universal structural argument; it does not use
  a bounded semigroup search or a characteristic-independent Betti-rank
  assertion. No issue was found that invalidates the proposed three-corner
  reduction.

## 6. Separate optional observation about degree-one terminals

The smallest non-\(m\) generator always satisfies

\[
\boxed{\operatorname{ord}(m+g_2)=2.}                         \tag{3}
\]

There is the displayed factorization of length two. In a hypothetical
factorization of length at least three, a non-\(m\) generator would contribute
at least \(g_2\), and the other at least two generators would contribute at
least \(2m\), giving a total greater than \(m+g_2\). Therefore such a
factorization would have to use only \(m\), forcing \(g_2\) to be a
positive multiple of \(m\), contrary to minimality. This proves (3).

Also \(\operatorname{ord}(2m)=2\), simply because three generators have
sum at least \(3m\). Thus neither \([m]\) nor \([g_2]\) lies in
\((0:_Gx)_1\). These are two distinct members of the degree-one coordinate
basis \([g_1],\ldots,[g_e]\); every other degree-one terminal is one of the
remaining \(e-2\) coordinates. Since different coordinates have different
successor values, their nonzero images cannot cancel. Consequently the
degree-one terminal count satisfies the universally stronger bound

\[
\boxed{\ell=\dim_k(0:_Gx)_1\le e-2.}                       \tag{4}
\]

Using the already established identity
\(H_1=\delta-q_2+\ell\), this would improve the first estimate of (5.3) to
\(H_1\le M-q_2-1\), where \(M=m-1\). Observation (4) is independent
of maximal quadratic dimension and is not needed for the Sidon proof or the
three exclusions above.
