# Higher harmonic module bounds and independent review of the all-rank gate

## Status

The new all-rank Catalan gate in `../differential/HARMONIC_FIRST_GATE_PAYS_ALL_RELATIVE_RANKS.md` passes this independent mathematical review, with its explicitly named classical consecutive-cancellation input. The proof uses that stronger input correctly; raw coefficientwise Betti domination alone would not suffice.

A sharper finite-module estimate is proved below. It improves some higher-rank resource bounds, including the residual parameter example `(e,δ,r)=(274,17,6)`, but does not pay the first rank there and does not close unrestricted P14.

## 1. The external input was checked at a primary author source

The author-hosted Caviglia–Kummini paper *Poset embeddings of Hilbert functions and Betti numbers* is available at

https://www.math.purdue.edu/~gcavigli/Articles-PDF/%5BM13%5D.pdf

Its Introduction, printed page 2, explicitly states the homogeneous-ideal to same-Hilbert-function lex-ideal consecutive-cancellation theorem and cites Peeva, Theorem 1.1. The general setup is a field k without a characteristic-zero assumption. Proposition 3.9 and Lemma 3.10, printed pages 6–7, establish their corresponding extension and describe cancellations by adjacent homological positions. The characteristic-zero assumption in Discussion 2.4 concerns a separate general-hypersurface restriction assertion. It is not an assumption of the polynomial-ring lex cancellation assertion used here.

The original named theorem is I. Peeva, *Consecutive cancellations in Betti numbers*, Proc. Amer. Math. Soc. **132** (2004), no. 12, 3503–3507, DOI 10.1090/S0002-9939-04-07517-3. Its official publisher PDF was not directly retrieved. This review uses the primary Caviglia–Kummini statement and development of the theorem, consistently with the differential note's explicit dependency declaration.

## 2. A sharper harmonic inequality for every generic rank

Let P be a polynomial ring in r variables over any field. If a finite graded P-module X is minimally generated in one degree a, then, for `1<=j<=r-1`,

    c_j(X) <= C(r-1,j) sum_{n>=0} [j/(n+j)] dim X_{a+n}.       (H)

All rational coefficients here are ordinary real/rational inequalities, not scalars used in a positive-characteristic rank calculation.

First take the homogeneous initial submodule of the kernel of a minimal presentation `P(-a)^q -> X`. Generic ranks can only increase in this degeneration: at each internal degree, the Koszul chain dimensions are fixed and

    c_j = alternating partial sum of chain dimensions - rank(∂_{j+1}).

A specialization cannot increase the boundary rank. The initial quotient is a direct sum of q shifted Artin cyclic quotients `P/I_i`. It therefore suffices to prove (H) for a cyclic quotient. Use the named consecutive-cancellation theorem to replace I by its same-Hilbert-function lex ideal L. Each adjacent cancellation decreases exactly one c_j and leaves the other c-indices unchanged. Consequently `c_j(P/I)<=c_j(P/L)`.

Write D for the standard monomial order ideal of P/L, and `D^(s)=D intersect k[x_1,...,x_s]`. A useful exact stable-ideal identity is

    c_j(P/L)=sum_{s=j}^{r-1} C(s-1,j-1) length(D^(s)).        (S)

Indeed, Eliahou–Kervaire and the partial alternating binomial identity give

    c_j(P/L)=sum_{u in G(L), max(u)>=2} C(max(u)-2,j-1).

For every standard monomial v in the first s variables, the finite x_(s+1)-chain starting at v ends at a unique generator of L with largest variable s+1. This terminal is minimal: if dividing it by a smaller variable entered L, stability would force its division by x_(s+1) into L, contradicting the choice of terminal. The correspondence is bijective. Thus the number of such generators is `length(D^(s))`, proving (S).

The standard monomials of a strongly stable ideal are closed under increasing the variable indices. For each degree n, this implies the normalized alphabet-density inequality

    #D_n^(s)/C(s+n-1,n) <= #D_n/C(r+n-1,n).                 (A)

Here is an explicit probability proof, avoiding any characteristic argument. Uniform degree-n monomials in s variables correspond to uniform n-subsets of `[s+n-1]` by the stars-and-bars bijection `b_i=a_i+i-1`, where `a_1<=...<=a_n` are their variable indices. A uniform n-subset B of `[N]` can be coupled to a uniform n-subset of `[N+1]` by keeping B with probability `(N+1-n)/(N+1)`, and otherwise replacing a uniformly chosen member of B by N+1. Every output n-subset has probability `1/C(N+1,n)`, and every ordered coordinate can only increase. Iterating from s to r gives a monotone coupling of uniform monomials. Since membership in D is preserved by increasing indices, (A) follows.

Apply (A) degree by degree in (S). The exact coefficient identity is

    sum_{s=j}^{r-1} C(s-1,j-1) C(s+n-1,n)
       = [j/(n+j)] C(r-1,j) C(r+n-1,n).

It follows by rewriting the summand as

    C(n+j-1,j-1) C(s+n-1,n+j-1)

and using the hockey-stick identity. This proves (H). Equality holds for every quotient `P/P_+^D`, because its standard sets are full through degree D-1 and every step above is then an equality.

## 3. Exact transfer of (H) to the actual tower

Retain the actual tower and weighted resource S. Put

    h_{s,t}=dim (X_s)_{s+t},
    sum_s h_{s,0}=δ,
    sum_{s,t} h_{s,t}=S,
    h_{s,t}<=q_s C(r+t-1,t).

For `j>=2`, the exact tower transfer used in the all-rank gate is

    c_j(G)<=L_j+sum_s c_j(X_s)+sum_s c_(j-1)(M_s),
    L_j=e C(r-1,j)-C(r,j+1),
    M_s=(X_s)_(>=s+1).

The module M_s is generated in degree s+1, so (H) applies to it with relative degree t-1. Therefore

    c_j(G)<=L_j+sum_s sum_{t>=0} A_j(t) h_{s,t},           (T)

where

    A_j(0)=C(r-1,j),
    A_j(t)=C(r-1,j) j/(t+j)
            +C(r-1,j-1)(j-1)/(t+j-2),       t>=1.

For each `D>=1`, choose `alpha=A_j(D)` and put

    B=A_j(0)-alpha
       +sum_{t=1}^{D-1}(A_j(t)-alpha) C(r+t-1,t).

The weights A_j(t) decrease for t>=1. Since h_(s,0)=q_s exactly, while the higher h-values have the displayed upper caps, (T) proves the explicit affine bound

    c_j(G)<=L_j+alpha*S+B*δ
           <=L_j+δ(alpha*V+B),
    V=e+δ/2-3/2.                                        (U)

The constant term `A_j(0)-alpha` is allowed to be negative: its multiplicity is exactly q_s, not merely bounded by q_s. One must not replace that exact equality by an upper bound when the coefficient is negative.

For j=1 retain `mu(M_s)<=r q_s` and use (H) only on X_s. This is the original first-rank harmonic family; the sharper higher-rank estimate introduces no first-rank improvement.

## 4. Fresh exact checks and a residual-size example

`verify_higher_harmonic.py` computes monomial Koszul boundary ranks independently in fields 2, 3 and 1009, rather than assuming EK for arbitrary monomial ideals. Its certificate is `HIGHER_HARMONIC_CERTIFICATE.json`.

The new checks passed:

- 1,347 harmonic or exact power-quotient identities;
- 1,095 exact EK-section identities for lex quotients;
- 1,915 normalized alphabet-density comparisons.

For `(e,δ,r)=(274,17,6)`, the choice D=5 in (U) gives:

| j | alpha | B | certified upper bound | target R_j |
|---:|---:|---:|---:|---:|
|2|27/7|967/3|559130/21|65450|
|3|85/12|995/2|540235/12|439285|
|4|410/63|2345/6|4926169/126|2095016|
|5|3|470/3|51802/3|7562247|

The top rank remains paid by the inherited universal scalar theorem. Thus all nonfirst rows are paid at this parameter point even though `δ=17<K(6)=21`. These are actual-source sufficient bounds conditional only on its actual hitting sextuple and the established tower inputs. They do not establish that such a source exists.

The same resource method gives a first-rank upper bound `40379/6`, which exceeds `R_1=6149`. This failure is a failure of the resource upper bound, not a genuine rank violation or a P14 counterexample.

## 5. Independent review of the differential all-rank Catalan theorem

Every step of `HARMONIC_FIRST_GATE_PAYS_ALL_RELATIVE_RANKS.md` was checked against the preceding derivation:

1. Its coarser all-j bound `C(r-2,j-1)(alpha*length+B*mu)` is valid by lex cancellation and EK.
2. Its base `L_j=(e-1)C(r-1,j)-C(r-1,j+1)` equals the independent expression `e C(r-1,j)-C(r,j+1)`.
3. Its actual tower bound (5) and the common-stratum transfer retain the correct rank indices; the j=r zero convention is consistent.
4. Under the first gate, replacing B by `2V/(r+1)` yields exactly `p+(3-4/(r+1))q`, before its coarser replacement by p+3q.
5. Its Gamma_j binomial-basis expansion has only nonnegative coefficients for d>=0, and the target difference is exact.
6. Its Vandermonde lower bound gives `d*p+d(d+1)q/2`, so d>=5 suffices. The sharper coefficient gives the claimed direct d3/r3 and d4/r4 cases.
7. Its small-defect subsets are genuinely selected within the actual E: each numerical quadratic coordinate hit by E has a live quadratic factorization involving an E-variable. At most δ selections suffice, and standard gradedness kills all higher degrees. Extending to triples or quadruples and applying same-source upward stability is legitimate.

A separate exact integer/rational script check verified the Gamma identity and binomial lower bound for 38,850 triples `3<=r<=39`, `1<=j<=r`, `0<=d<=49`, with no failure. The universal conclusions rest on the displayed proofs, not this finite box.

No global closure follows: the Catalan gate still grows rapidly in r, and the source's minimum actual hitting size is not universally bounded by a fixed constant.
