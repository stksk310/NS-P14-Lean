# R55: the dense torsion cap from classical microinvariants

## Scope and classical input

This note proves, for every genuine numerical semigroup of multiplicity
\(m\) and actual embedding dimension \(e\), the universal numerical cap

\[
 t=\dim_k(0:_G[m])\le
 \sum_{j=1}^{m-1}\min\left(m-e,\left\lfloor\frac{j-1}{2}\right\rfloor\right).
\tag{1}
\]

Consequently, if \(2e\ge m+2\), then

\[
 t\le(m-e)(e-2).
\tag{2}
\]

The numerical proof is independent of the coefficient field.  It uses
one classical theorem, not claimed as an R55 result: Juan Elias,
*On the deep structure of the blowing-up of curve singularities*,
Math. Proc. Cambridge Philos. Soc. **131** (2001), 227--240,
Theorem 3.3(i), DOI
[10.1017/S0305004101005217](https://doi.org/10.1017/S0305004101005217).
The author-uploaded complete primary paper is available at
[ResearchGate](https://www.researchgate.net/publication/231980177_On_the_deep_structure_of_the_blowing-up_of_curve_singularities).
The theorem bounds every microinvariant by
\(i^*(R)=\min\{m-e+1,i(R)\}\), with this definition immediately
before Proposition 3.2.  We use only the resulting bound
\(\max a_i\le m-e+1\).

The new step here is the exact connection between these microinvariants,
actual x-terminal counts, and the length distribution of shortest
least-offset residue paths.  Combining (2) with R55 compact lex payment
gives an all-field ordinary P14 theorem at every fixed embedding ratio
less than one, for sufficiently large multiplicity.  It does not settle
all ordinary sources, in particular a general regime of small defect
\(m-e\) relative to \(m\).

## 1. Actual numerical coordinates and microinvariants

Let \(\Gamma=\langle m=g_1<\cdots<g_e\rangle\), let \(G\) be its
tangent cone, and write \(\delta=m-e\).  For each residue
\(r\in\mathbb Z/m\mathbb Z\), define:

* \(w_r\): the least numerical element of \(\Gamma\) in residue r;
* \(s_r=\operatorname{ord}_\Gamma(w_r)\);
* \(d_r\): the least sum of offsets \(g_i-m\), \(i>1\), in residue r;
* \(l_r\): the shortest length of a word achieving that least offset;
* \(L_r=(w_r-d_r)/m\).

For residue zero all five numbers are zero.  For every other residue,
\(s_r\ge1\), and

\[
 s_r\le L_r\le l_r.
\tag{3}
\]

Indeed an actual maximal word for \(w_r\), after deleting multiplicity
letters if any, has offset at least \(d_r\), so
\(w_r-ms_r\ge d_r\).  A least-offset word of length \(l_r\) has
actual numerical weight \(d_r+ml_r\in\Gamma\), hence it is at least
\(w_r\), proving the other inequality.

Let \(R=k[[t^\Gamma]]\), with parameter \(X=t^m\).  Its first
neighborhood ring is

\[
 R'=k[[t^m,t^{g_2-m},\ldots,t^{g_e-m}]].
\]

The Apéry weights of its value semigroup are exactly \(d_r\).
As modules over \(W=k[[X]]\),

\[
 R=\bigoplus_r Wt^{w_r},\qquad
 R'=\bigoplus_r Wt^{d_r},\qquad
 R'/R=\bigoplus_r W/(X^{L_r}).
\tag{4}
\]

Thus the multiset of \(L_r\)'s is precisely the multiset of classical
microinvariants, including its zero.  Elias's theorem gives

\[
 0\le L_r\le\delta+1\quad\hbox{for every r}.
\tag{5}
\]

Elias works over an infinite residue field.  To apply his theorem to a
finite field k, replace k by the purely transcendental extension k(u).
All quantities in (3)--(4) are defined by the same numerical weights and
word lengths and are unchanged by this extension.  Therefore (5) holds
for the numerical quantities over every original field as well.  This
argument does not assume preservation of any unknown matrix rank.

## 2. Exact per-residue terminal inequality

Fix a nonzero residue r and put

\[
 q_r=l_r-L_r,\qquad
 a_r(q)=\operatorname{ord}_\Gamma(w_r+qm),\quad q\ge0.
\]

The least-offset word of length \(l_r\) has weight
\(w_r+q_rm=d_r+ml_r\).  It has actual order exactly \(l_r\): a
longer factorization would have smaller offset in the same residue,
contradicting the definition of \(d_r\).  After multiplying it by any
power of x=[m], the same argument gives

\[
 a_r(q)=L_r+q\quad(q\ge q_r).
\tag{6}
\]

In particular there are no dead x-arrows after index \(q_r-1\).  Let
\(t_r\) be the number of dead x-arrows in this residue; these arrows
are exactly the finite-string terminals.  Adding m always raises order
by at least one.  Therefore

\[
 \sum_{q=0}^{q_r-1}[a_r(q+1)-a_r(q)-1]
 =l_r-s_r-q_r=L_r-s_r.
\tag{7}
\]

Every summand is a nonnegative integer, and every dead arrow contributes
at least one.  There are only \(q_r\) positions in that sum.  Hence

\[
 t_r\le\min\{L_r-s_r,l_r-L_r\}
 \le\min\left\{\delta,
               \left\lfloor\frac{l_r-s_r}{2}\right\rfloor\right\}
 \le\min\left\{\delta,
               \left\lfloor\frac{l_r-1}{2}\right\rfloor\right\}.
\tag{8}
\]

The first entry in the middle minimum uses (5) and \(s_r\ge1\).
The other entry uses that the two entries of the first minimum have
sum \(l_r-s_r\).  Thus no bound on finite-string lengths, torsion
generators, or higher relative Tor ranks is being substituted for t.

## 3. Shortest-path length distribution and the dense cap

Arrange the \(m\) lengths \(l_r\) in nondecreasing order as
\(l_{(0)},\ldots,l_{(m-1)}\).  Then

\[
 l_{(j)}\le j,\qquad0\le j\le m-1.
\tag{9}
\]

To see this, any prefix of a shortest least-offset word is itself a
shortest least-offset word in its residue: a smaller offset, or an
equal offset with fewer letters, could replace that prefix and improve
the full word.  Its prefix residues are distinct, since any positive
offset cycle could be removed to lower the full offset.  Thus a word
of length at least j supplies j distinct residues with lengths
0 through j-1.  Consequently at most m-j residues have length at least
j, which is equivalent to (9).

The function \(F(j)=\min\{\delta,\lfloor(j-1)/2\rfloor\}\) is
nonnegative and nondecreasing on positive integers.  Sum (8), use (9),
and use t_0=0 in residue zero.  This proves (1).

If \(m\ge2\delta+2\), evaluate the sum exactly.  At lengths
1 through \(2\delta\), the values are
0,0,1,1,...,\(\delta-1,\delta-1\); all subsequent values are
\(\delta\).  Hence

\[
 \sum_{j=1}^{m-1}F(j)
 =\delta(\delta-1)+\delta(m-1-2\delta)
 =\delta(m-\delta-2)=\delta(e-2).
\tag{10}
\]

The case \(\delta=0\) is immediate and included.  This proves (2).
The same evaluation also works at the one-step boundary
\(m=2\delta+1\), but the simpler stated condition is sufficient for
the large dense ordinary chamber.

## 4. New compact-lex ordinary comparison

Retain \(A=G/xG\), \(a=\dim A_2\le\delta\), and let

\[
 p=\min\{q\ge1:\binom{q+1}{2}\ge a\},\qquad
 S(m)=(m+1)H_m-(5m-1)/2.
\]

The zero-quadratic case is immediate as in the compact-lex note.  For
\(a>0\), its exact all-row proof applies with ANY proved upper bound
for t in place of its older bound tau.  Substitute (2), and use

\[
 \Delta-\delta(e-2)=\frac{\delta(\delta+3)}2,
 \qquad\Delta=\binom m2-\binom e2.
\tag{11}
\]

**Theorem.** If \(2e\ge m+2\), the actual interval target is ordinary,
and

\[
 (p-1)S(m)\le\frac{\delta(\delta+3)}2,
\tag{12}
\]

then \(\beta_i(G;k)\le i\binom m{i+1}\) in every field and every
row.  The criterion is field-independent; p may be replaced by the
larger numerical \(p_\delta\) from the compact-lex note.

Here is a convenient entirely integer parameter condition.  Put
\(b=\lceil\log_2m\rceil\).  Since
\(p-1<\sqrt{2\delta}\), \(S(m)\le m\log m\le mb\),

\[
 \boxed{\quad2e\ge m+2,\qquad
        \delta^3\ge8m^2b^2\quad}
\tag{13}
\]

implies (12).  Indeed squaring the desired inequality
\(\sqrt{2\delta}\,mb\le\delta^2/2\) gives exactly the cubic
condition in (13).  This is a sufficient condition, not a necessary
one.

For every fixed \(\epsilon>0\), (13) holds for all sufficiently large
m whenever \(\delta\ge\epsilon m\) and \(2e\ge m+2\), since
\(b^2/m\to0\).  Together with the inherited unconditional sparse
ordinary range, this yields ordinary P14 for every fixed embedding
ratio less than one at sufficiently large multiplicity.  More
intrinsically, (13) reaches the dense range
\(\delta\ge2m^{2/3}\lceil\log_2m\rceil^{2/3}\).

This leaves an actual quantitative gap when the multiplicity defect is
smaller.  Neither (1), (2), nor the compact-lex theorem asserts the
joint sharp inequality needed there.  The sparse counterexample
\(\langle7,9,20\rangle\) has \(2e<m+2\), so it is fully consistent
with (2).

## Verification and proof origin

The identity (4) and Elias's cited theorem supply the classical input.
All per-residue string counts, shortest-path counting, exact sum
evaluation, and compact-lex target assembly are proved above.  Finite
Kunz-box tests are supplementary; the millions of nonviolations in the
earlier branch note are not used as a proof of (1) or (2).
