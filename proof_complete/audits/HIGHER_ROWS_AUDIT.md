# Primitive four-generator higher rows: independent audit

2026-11-09. This note proves the source bounds, the stable tail, and the
exhaustiveness of the remaining finite certificate directly from definitions.
It audits the higher-row part of R26-A01 (historical object
`b76ca9ec6f5fde4985e1b5153df77a247d33421de5cbca630e7a7c90af8c080c`).
It does not use the historical author's acceptance or status statements as
mathematical evidence. The auxiliary endpoint construction below also supplies
the portion needed from R24-N01. No R25 graph-rank, total-unimodularity, or
complete transferred-differential theorem is needed.

## 1. Statement and one external target input

Let

\[
0<a<b<w<m,\qquad \gcd(a,b,w)=1,
\quad \Gamma=\langle m,m+a,m+b,m+w\rangle.
\]

Let \(k\) be any field, \(G=\operatorname{gr}k[[\Gamma]]\),
\(S=k[x,y,z,v]\), \(A=k[x,v]\), and \(B=k[y,z]\). All four
generators are minimal: they are distinct elements of \([m,2m)\).
Their gcd is 1. Write

\[
Q=G/(x,v)G,\quad P=\dim_kQ,\quad
R=\dim_k(0:_G(x,v)),\quad
\sigma=\dim_k(0:_Q(y,z)).
\]

The result is

\[
\beta_i^S(G)\le F_i(m,w)\qquad(i\ge2),
\tag{H}
\]

including the requested true-narrow subrange \(w\le m-2\).
Here \(F_i\) is the Betti number of the actual interval completion
\(\langle m,m+1,\ldots,m+w\rangle\), over its own \(w+1\)
variables. The only input about that target used in this note is its exact
arbitrary-field formula

\[
F_i=i\binom w{i+1}+
\begin{cases}
(D+1-i)\binom w{i-1},&i\le D,\\
(i-D)\binom wi,&i>D,
\end{cases}
\quad D=w-((m-1)\bmod w)\in\{1,\ldots,w\}.
\tag{T}
\]

The parent audit separately checks this target input against
Gimenez–Sengupta–Srinivasan, arXiv:1108.3203, Theorem 4.1 (arbitrary field),
and Herzog–Stamate, arXiv:1308.4644v3, Proposition 2.5 (the arithmetic
sequence ideal and its tangent-cone ideal have equal Betti numbers). All
source statements, capacity lower bounds from (T), and the finite certificate
are proved here.

## 2. Exact homogeneous-offset core and actual competition

Use the homogeneous offset semigroup algebra

\[
C=k[s,st^a,st^b,st^w].
\]

For a monomial \(s^dt^n\in C\), put \(r=n\bmod w\),
\(\epsilon_r=\mathbf1_{r>0}\), and write uniquely

\[
n=r+Kw,\quad d=L+K+\epsilon_r,\qquad L,K\ge0.
\]

Nonnegativity follows from \(0\le n\le dw\). Multiplication by
\(x=s\) and \(v=st^w\) increases respectively \(L\) and \(K\).
Let \(M_r\subset k[x,v]\) consist of the coordinate monomials occurring
in residue \(r\). Each \(M_r\) is an ideal and

\[
C\simeq\bigoplus_{r=0}^{w-1}M_r[\epsilon_r,r]
\tag{2.1}
\]

as an \(A\)-module. In particular \(M_0=A\). The gcd assumption
ensures every residue is reachable, so every \(M_r\ne0\).

For clarity, the map from this core to the actual tangent cone is not assumed
injective. If \(\nu(N)\) denotes the maximum decomposition length of
\(N\in\Gamma\), the graded surjection \(C\to G\) sends
\(s^dt^n\) to the degree-\(d\) class of \(t^{dm+n}\). Its image is
nonzero precisely when \(\nu(dm+n)=d\). In each fixed degree, distinct
offsets give distinct actual weights. Its kernel is consequently a monomial
ideal of \(C\).

Fix \(r\) and \(j\ge1\), and set

\[
r_j=(r-jm)\bmod w,\qquad
\kappa_{r,j}=(jm+r_j-r)/w.
\]

A monomial with coordinates \((L,K)\in M_r\) has a longer expression
of length \(d+j\) exactly when some minimal generator
\((u,q)\in\operatorname{Min}M_{r_j}\) satisfies

\[
K\ge q+\kappa_{r,j},\qquad
L\ge u-j-\kappa_{r,j}+\epsilon_{r_j}-\epsilon_r.
\tag{2.2}
\]

Indeed the longer expression has offset \(n-jm\), whose coordinates are
\(K'=K-\kappa\) and
\(L'=L+j+\kappa+\epsilon_r-\epsilon_{r_j}\). Membership in
\(M_{r_j}\) is equivalent to divisibility by one of its minimal generators.
Define

\[
T_r=\bigl(
x^{\max(0,u-j-\kappa_{r,j}+\epsilon_{r_j}-\epsilon_r)}
v^{q+\kappa_{r,j}}:
j\ge1,\ (u,q)\in\operatorname{Min}M_{r_j}
\bigr).
\]

Thus, without replacing any column by a free column,

\[
N_r=M_r\cap T_r,\qquad
G\simeq\bigoplus_r M_r/N_r[\epsilon_r,r]
\tag{2.3}
\]

as \(A\)-modules. Since \(m>w\), integrality and
\(jm+r_j-r> (j-1)w\) imply \(\kappa_{r,j}\ge j\).
This also proves the nonnegativity of every displayed \(v\)-exponent.
These arguments already work at \(m=w+1\); true narrow only needs
\(m\ge w+2\).

## 3. Every minimal internal word has length at most w-2

A nonempty zero-sum subword of internal offsets has length \(\ell\)
and offset \(qw\), with \(1\le q\le\ell-1\), because each letter
is strictly between 0 and \(w\). Replacing it by
\(x^{\ell-q}v^q\) preserves degree and offset and produces positive
endpoint factors. A word admitting such a subword cannot be a minimal
\(A\)-generator.

Consider a mixed word of length \(w-1\). Suppose its multiset has no
nonempty zero-sum submultiset in \(\mathbb Z/w\mathbb Z\). For any
ordering, the \(w\) prefixes, including the empty prefix, have pairwise
distinct residues, hence exhaust the group. Choose an ordering with two
different adjacent letters and interchange them. Exactly one intermediate
prefix changes, and its new residue differs from the old residue. The other
\(w-1\) residues have not changed, so the new prefix coincides with one
of them. This yields a zero-sum contiguous subword in the new ordering,
contradicting the assumption on the multiset. Therefore every mixed word
of length \(w-1\) is nonminimal.

For \(y^{w-1}\), if \(g=\gcd(a,w)>1\), the factor \(y^{w/g}\)
is already an endpoint word; its endpoint factors are both positive.
If \(\gcd(a,w)=1\), there is a unique \(q\in\{2,\ldots,w-1\}\)
with \(qa\equiv b\pmod w\). Write \(qa=b+hw\). Because
\(0<a,b<w\), necessarily \(0\le h\le q-1\). Then

\[
y^q=x^{q-1-h}zv^h
\]

in \(C\), with a positive total of \(q-1\) endpoint factors.
So \(y^{w-1}\) is nonminimal. Interchanging \(a,b\) proves the same
for \(z^{w-1}\). Any longer internal word has a length-\(w-1\)
factor and is also nonminimal.

Consequently the minimal generators of all \(M_r\) are represented
by internal words of length at most \(w-2\). For \(r>0\), their
coordinates obey

\[
L+K\le w-3;\qquad \operatorname{Min}M_0=\{(0,0)\}.
\tag{3.1}
\]

There cannot be a relation between two distinct pure internal words with
the same degree and offset: the equations
\(u+z=u'+z'\), \(au+bz=au'+bz'\), with \(a\ne b\), force
the exponent pairs to agree. Hence both \(C/(x,v)C\) and the further
quotient \(Q\) are monomial Artin quotients of \(k[y,z]\).
Every standard word of \(Q\) has degree at most \(w-2\), giving

\[
P\le\sum_{d=0}^{w-2}(d+1)=\binom w2.
\tag{3.2}
\]

Different socle words of a two-variable monomial quotient have different
\(y\)-exponents: if two had the same exponent, the smaller would divide
the larger and could not be killed by \(z\). These exponents belong to
\(\{0,\ldots,w-2\}\), so

\[
\sigma\le w-1.
\tag{3.3}
\]

This proves the original shortened-word step without invoking the
Savchev–Chen theorem needed elsewhere for the first row.

## 4. Common endpoint socle bound

For \(r=0\), the \(x\)-exponent in every generator defining \(T_r\)
is at most \(A_0=\max(w-4,0)\). If \(r_j=0\), the exponent is
zero. Otherwise (3.1) gives
\(u-j-\kappa+1\le w-3-2j+1\le w-4\).
For \(r>0\), terms with \(r_j=0\) again have exponent zero; the
other terms have exponent at most
\(w-3-2j\le w-5\). Thus their bound is
\(A_1=\max(w-5,0)\).

The inclusion \(M_r\hookrightarrow A\) induces

\[
M_r/(M_r\cap T_r)\hookrightarrow A/T_r.
\]

Its common \((x,v)\)-socle is a subspace of that of \(A/T_r\).
For a two-variable monomial ideal whose minimal generators have
\(x\)-exponents at most \(A\), each finite socle corner is between
two successive staircase generators. Its \(x\)-coordinate belongs to
\(\{0,\ldots,A-1\}\), and these coordinates are distinct. This
argument works even if the quotient is not Artinian. There are at most
\(A\) such corners. Summing the residue columns gives

\[
R\le \max(w-4,0)+(w-1)\max(w-5,0).
\tag{4.1}
\]

In particular \(R=0\) for \(w=3,4\), and for \(w\ge5\),

\[
R\le w^2-5w+1.
\tag{4.2}
\]

No socle is counted in an unrelated quotient, and no actual source top
Betti number is set to zero without the stated width restriction.

## 5. General double-complex bounds over every field

The \(A\)-module \(G\) is finitely generated by Section 3 and has
rank zero: \(v^m=0\) because the weight \(m(m+w)\) of that word
also has an expression of length \(m+w>m\). Its zeroth and second
\(A\)-Betti numbers are respectively \(P\) and \(R\), the latter
by the last homology of \(K(x,v;G)\). Euler characteristic of a
finite free \(A\)-resolution gives

\[
\beta^A(G)=(P,P+R,R).
\tag{5.1}
\]

Split the actual Koszul complex \(K(x,y,z,v;G)\) into the endpoint
and internal directions. On the page obtained by taking endpoint
homology, its row dimensions are
\(\beta^A_q(G)\binom2p\). On the next page, the row \(q=0\)
is exactly \(H_p(y,z;Q)\). Since \(Q\) is an Artin quotient
of \(B\), its \(B\)-Betti numbers are

\[
\beta^B(Q)=(1,\sigma+1,\sigma).
\tag{5.2}
\]

Here the last entry is the Koszul socle, the first is cyclicity, and
Euler characteristic gives the middle entry. The other two rows on that
page have dimensions at most their preceding-page dimensions. Every later
page can only decrease dimensions. Therefore

\[
\beta_i^S(G)\le
\beta_i^B(Q)+(P+R)\binom2{i-1}+R\binom2{i-2}.
\tag{5.3}
\]

The binomial coefficient is zero outside \(0,1,2\), and so is
\(\beta_i^B(Q)\) outside \(0,1,2\). In particular,

\[
\boxed{\beta_2\le2P+3R+\sigma,\quad
\beta_3\le P+3R,\quad \beta_4\le R.}
\tag{5.4}
\]

This is the full spectral-sequence argument, rather than an assumption
that the second differential vanishes. It needs no transferred endpoint
matrix. Each bound holds separately over the chosen arbitrary field.
The quantities \(P,R,\sigma\) are monomial basis counts, so they are
independent of the characteristic; the argument does not require all
\(S\)-Betti numbers themselves to be characteristic independent.

## 6. Exact capacity inequalities

For \(w\ge3\), formula (T) gives

\[
F_2\ge2\binom w3+w.
\tag{6.1}
\]

Indeed, if \(D\ge2\), the additional term is
\((D-1)w\ge w\). If \(D=1\), it is
\(\binom w2\ge w\). The minimum is attained at \(D=2\).
For \(w\ge5\), similarly

\[
F_3\ge3\binom w4+\binom w2.
\tag{6.2}
\]

For \(D\ge3\) the extra term is at least \(\binom w2\);
for \(D=2\) it is \(\binom w3\ge\binom w2\), because
\((w-2)/3\ge1\); for \(D=1\) it is even larger. Also
\(F_4\ge4\binom w5\) since the extra term is nonnegative.

For \(w\ge5\), (3.2), (3.3), and (4.2) give

\[
\beta_2\le4w^2-15w+2,\quad
\beta_3\le(7w^2-31w+6)/2,\quad
\beta_4\le w^2-5w+1.
\]

With \(u=w-11\), the second-row difference satisfies the exact identity

\[
3\left(2\binom w3+w-(4w^2-15w+2)\right)
=u^3+18u^2+83u+60>0\quad(u\ge0).
\tag{6.3}
\]

With \(u=w-5\), the third- and fourth-row differences satisfy

\[
8\left(3\binom w4+\binom w2-(7w^2-31w+6)/2\right)
=u^4+14u^3+47u^2+34u+96>0,
\tag{6.4}
\]

\[
30\left(4\binom w5-(w^2-5w+1)\right)
=u^5+15u^4+85u^3+195u^2+124u+90>0.
\tag{6.5}
\]

Their coefficients are independently recomputed by exact rational
polynomial arithmetic in the new checker, with no finite-grid inference.
For \(w=4\), \(R=0\) and \(P\le6\), so
\(\beta_3\le6<7=\min F_3\), and \(\beta_4=0\).
For \(w=3\), the only internal pair is \((a,b)=(1,2)\), so the
source is the target. For \(i>4\), source Betti numbers vanish by
the four-variable Koszul complex. Only \(\beta_2\), \(4\le w\le10\),
remains to be checked.

## 7. All-m stability and a genuine finite reduction

If \(m\ge w(w-2)\), then for every \(0\le r<w\) and \(j\ge1\),

\[
\kappa_{r,j}\ge j(w-2)\ge w-2.
\]

This follows by integrality from
\(jm+r_j-r\ge jw(w-2)-(w-1)\).
In the definition of \(T_r\), every \(x\)-exponent is consequently
zero: if \(r_j>0\), it is bounded above before truncation by
\((w-3)-1-(w-2)+1=-1\), and if \(r_j=0\) it is negative as well.
All \(v\)-exponents are at least \(w-2\). Thus

\[
T_r=(v^{t_r}),\qquad t_r\ge w-2.
\]

Every minimal generator of \(M_r\) has \(v\)-exponent at most
\(w-3\) by (3.1); the unique generator in residue zero has exponent
zero. None is forbidden. Moreover, if a monomial belongs to
\(M_r\cap(v^{t_r})\), any minimal \(M_r\)-generator dividing it
has smaller \(v\)-exponent, so the monomial belongs to \(vM_r\).
Consequently the kernel \(C\to G\) is contained in \(vC\), and

\[
Q\cong C/(x,v)C,\qquad
P=\sum_r\mu(M_r).
\]

Finally \(M_r/(M_r\cap(v^{t_r}))\) embeds in \(A/(v^{t_r})\), on
which multiplication by \(x\) is injective. Hence

\[
\boxed{m\ge w(w-2)\Longrightarrow
R=0,\quad Q\cong C/(x,v)C.}
\tag{7.1}
\]

The isomorphism is an isomorphism of internal \(B\)-algebras, so
\(\sigma\) is stable too. One core computation per offset pair pays
the whole tail; the target is compared to its minimum over all residues of
\(m\), not just the tail onset.

For completeness, the historical finite competition cutoff is also valid.
Set \(J_0=\lfloor(w-2)/2\rfloor\) and
\(p=w/\gcd(m,w)\). For \(j>J_0\), all \(x\)-thresholds are zero,
by (3.1) and \(\kappa\ge j\). Also
\(r_{j+p}=r_j\) and
\(\kappa_{r,j+p}=\kappa_{r,j}+m/\gcd(m,w)\).
So for such \(j\), the generators at \(j+p\) are divisible by the
corresponding generators at \(j\). Thus \(1\le j\le J_0+p\)
suffices to compute every competition ideal exactly. The new checker does
not rely on this cutoff: it uses the different actual-order cutoff in the
next section.

## 8. Independent actual-order computation and its stopping proof

The new executable `check_higher_rows.py` imports only Python's standard
library. It reads no historical checker or certificate. It reconstructs
\(P,R,\sigma\) directly from actual maximum orders, rather than from
(2.2) or the author's endpoint tables.

For each residue \(\rho\bmod m\), let \(b_\rho\) be the least
element of \(\langle a,b,w\rangle\) in that residue. Let
\(\ell_\rho\) be the shortest number of letters \(a,b,w\) expressing
\(b_\rho\). Lexicographic Dijkstra on the finite residue graph computes
these pairs exactly: all edge weights are positive and the gcd assumption
makes every vertex reachable. Put
\(T_\rho=b_\rho+m\ell_\rho\) and \(E=\max_\rho T_\rho\).

For every \(N\equiv\rho\pmod m\) with \(N\ge T_\rho\),

\[
\nu(N)=(N-b_\rho)/m.
\tag{8.1}
\]

To prove the upper bound, an expression of length \(d\) has offset
\(N-dm\in\langle a,b,w\rangle\), hence offset at least
\(b_\rho\). For the lower bound, use an expression of \(b_\rho\)
with \(\ell_\rho\) nonzero offsets and add the requisite number of
zero-offset multiplicity generators. This is possible exactly when
\((N-b_\rho)/m\ge\ell_\rho\). Below \(E\), elementary integer
dynamic programming in the four actual generators computes \(\nu\).
The checker verifies agreement of this DP and (8.1) at every finite overlap.
This proves that the implemented order function is exact on all integers.

For each internal word of degree \(d\le w-2\), with actual weight
\(N=u(m+a)+z(m+b)\), its class belongs to the standard basis of \(Q\)
exactly when

\[
\nu(N)=d,\quad
\nu(N-m)\ne d-1,\quad \nu(N-m-w)\ne d-1.
\]

The empty word is handled separately. One extra degree \(w-1\) is
examined as a regression of the proven word bound. Socle words are exactly
the standard exponent pairs with neither immediate successor standard.

The common endpoint socle is counted by scanning every actual weight
\(0\le N\le E\) for

\[
\nu(N)\ge0,\quad
\nu(N+m)>\nu(N)+1,\quad
\nu(N+m+w)>\nu(N)+1.
\tag{8.2}
\]

This scan is exhaustive: at \(N\ge T_\rho\), (8.1) gives
\(\nu(N+m)=\nu(N)+1\), so \(x\) is not zero there. Multiplication
by each generator sends a basis weight to a distinct basis weight or to
zero. Thus its kernel, and the common kernel, are spanned by the basis
weights tested in (8.2), in every characteristic. This directly counts
\(R\), without using historical jump-height or endpoint-socle code.

The tail core is separately enumerated by homogeneous degree and reachable
offsets in \(\{0,a,b,w\}\). It is also checked against the minimal
coordinate generators of the \(M_r\), and against the actual-order
invariants at the first stable multiplicity. These are consistency checks;
the all-tail claim rests on (7.1), rather than on matching sampled tails.

## 9. Coverage, results, and audit conclusion

For each \(w=4,\ldots,10\), enumerate every
\(1\le a<b\le w-1\) satisfying \(\gcd(a,b,w)=1\), and every
integer

\[
w+1\le m<w(w-2).
\]

The remaining multiplicities are precisely the stable tail (7.1). The
counts and independently recomputed maxima are:

| w | primitive pairs | finite m>w points | true-narrow points | max 2P+3R+sigma, including tails | min F2 | slack |
|---:|---:|---:|---:|---:|---:|---:|
|4|3|9|6|12|12|0|
|5|6|54|48|16|25|9|
|6|9|153|144|20|46|26|
|7|15|405|390|24|77|53|
|8|18|702|684|30|120|90|
|9|27|1431|1404|35|177|142|
|10|30|2070|2040|41|250|209|
|total|108|4824|4716||||

These pair counts also have a separate arithmetic check. For \(w>1\),
the number of ordered residue pairs \((a,b)\bmod w\) with
\(\gcd(a,b,w)=1\) is the Jordan totient
\(J_2(w)=w^2\prod_{p\mid w}(1-p^{-2})\). Among them, each of
\(a=0\), \(b=0\), and \(a=b\) removes \(\varphi(w)\) pairs;
these three subsets are disjoint within the primitive pairs. Dividing by
two for \(a<b\) gives \((J_2(w)-3\varphi(w))/2\), which evaluates
to the seven displayed pair counts. The number of multiplicities per pair
is \(w^2-3w-1\), independently reproducing every finite-point count.

There is one tail per primitive pair, hence 108 tails. The original 4,824
points include exactly 108 ordinary boundary points \(m=w+1\); omitting
those leaves exactly the requested 4,716 true-narrow points. This enlarged
finite campaign does not weaken any of the requested hypotheses.

On every finite point and every tail the new checker verifies
\(2P+3R+\sigma\le2\binom w3+w\). Thus (5.4) pays the remaining
second row. Sections 5–6 pay all other higher rows. This proves (H), with
the sole outside input (T) explicitly isolated.

The independent direct-order controls include
\((P,R,\sigma)=(5,0,2),(6,0,2),(37,7,2),(101,17,2)\) for the four
historical low-width and non-CM examples. In particular the new source
count retains actual nonzero common endpoint socles.

No mathematical defect was found in the R26-A01 higher-row reduction.
The qualification is computational proof with an explicit exhaustive finite
certificate, rather than a formal proof-assistant kernel result. The
finite reduction itself, all tail multiplicities, and characteristic
universality are justified before the integer enumeration is used.

Reproduction:

```sh
python n4_work/higher_rows/check_higher_rows.py --output n4_work/higher_rows/direct_order_certificate.json
```

The run completed with `PASS`, 4,824 finite points and 108 tails. Its
mathematical-payload SHA-256 is
`44dae4892039cec415b1edcfba6367d97d655e37f3ae559ad1f5e3842b9c16e5`.
The full run under `python -O` produced exactly the same mathematical
payload. Every finite and tail tuple \((P,R,\sigma,2P+3R+\sigma)\)
also agrees with the previously restored independent direct-order
certificate; that historical file was read only for this final comparison,
after the new computation. `AUDIT_RESULT.json` retains the compact receipt.

