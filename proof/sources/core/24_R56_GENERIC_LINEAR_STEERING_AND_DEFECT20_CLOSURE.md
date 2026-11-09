# Generic linear steering, head dimension twenty, and a sharper fixed-defect tail

## 1. Main conclusions and precise scope

Let G be an actual numerical semigroup tangent cone, multiplicity m, actual embedding dimension e, defect d=m-e, over any field. Put A=G/xG for x=[m], and let

    a=dim A2 <= d,
    p(a)=max{p>=0 : C(p+1,2)<=a},
    r(a)=max(3,p(a)),
    H(r)=C(2r,r)+r^2-r+1.

For e>=4 and d>=5, the following is a new all-field sufficient condition for every P14 row against the actual ordinary interval target:

    2e+d >= H(r(a)).                                      (1)

The forms used to establish (1) are non-x linear combinations; they need not be numerical generator variables. The proof does not reuse numerical-coordinate partial matching or total unimodularity for these forms.

Consequences, retaining the explicitly accepted inherited closures e<=273 and d<=16:

* Every genuine source with an actual ordinary target and a<=20 satisfies P14 over every field.
* In particular, every actual ordinary source with d<=20 satisfies P14. This extends the inherited ordinary low-defect boundary from16 to20; d17,...,20 are the new assembly consequence.
* For every fixed d>=5, put

      r_d=max(3,max{p:C(p+1,2)<=d}).

  Then the explicit fixed-defect tail

      2e+d>=H(r_d)                                        (2)

  pays all ordinary sources. Its threshold grows as exp(O(sqrt(d))), improving the exp(O(sqrt(d) log d)) form of the prior R55 coarse fixed-defect tail.

These are ordinary-source statements. Any assembly with previously accepted nonordinary/narrow closure should be stated separately. No unrestricted all-defect global P14 conclusion follows.

## 2. Named external and inherited dependencies

The all-rank chamber used below is proved in `HARMONIC_FIRST_GATE_PAYS_ALL_RELATIVE_RANKS.md`; its named external generic-rank input is Peeva's lex consecutive-cancellation theorem, with Eliahou–Kervaire and the actual numerical microinvariant inputs as specified there.

The additional named input here is **Green's hyperplane restriction theorem for a polynomial ring over an infinite field**, in its degree-two form. Primary verification is Caviglia–Kummini, *Poset embeddings of Hilbert functions and Betti numbers*, Section2.4,p3, author-hosted PDF https://www.math.purdue.edu/~gcavigli/Articles-PDF/%5BM13%5D.pdf . That paragraph states the polynomial-ring Green inequality over an infinite field and distinguishes the later characteristic-zero restriction for more general embedded quotient rings. It also cites Gasharov's arbitrary-characteristic generic-form extension. We use only the polynomial-ring linear-form theorem, not the characteristic-zero quotient-ring variant.

The new work is the full-module extension of the numerical tower to linear steering forms, the exact degree-two iteration, and its combination with the all-rank chamber. Green's theorem itself and the inherited E273/D16 closures are not claimed as newly proved here.

## 3. Linear changes preserve the actual tower

Write S=k[Y_1,...,Y_(e-1)] for all actual non-x variables. The numerical ideals N and F_s in A are actual ideals, hence S-submodules. The equal-jump isomorphism between corresponding strata of N and T is an isomorphism of full S-modules, before selecting any steering subset.

Choose linearly independent non-x linear forms l_1,...,l_r, let P=k[l_1,...,l_r], and assume A/(l_1,...,l_r)A is square-zero. Every A/F_s remains a standard graded quotient generated over P in degrees0,1. Therefore all tail facts used in the harmonic proof remain true:

    mu_P(X_s)=q_s,
    mu_P(M_s)<=r q_s,
    length(M_s)=length(X_s)-q_s.

The exact truncation sequences are P-linear. The opposite-jump strata remain isomorphic P-modules after restricting the original full S-module isomorphism. The numerical q_s, weighted volume S, and its bound S<=d(e+d/2-3/2) are unchanged.

Koszul complexes on commuting linear forms satisfy the same x-first identity

    c_j^{k[x,l]}(G)=c_j^P(A)+c_(j-1)^P(T)-rho_(j+1),

with the actual induced rank over the chosen field. The harmonic initial-module and lex-cancellation arguments are statements about standard graded polynomial modules and require no numerical weight grading. The proof of the all-rank chamber consequently applies verbatim to these forms when d>=5.

The only assertions that do not extend are the stronger numerical-coordinate matching and the small-active-variable TU interpretation. Neither is used in this argument.

## 4. Why a paid linear cut pays the intrinsic full Betti numbers

Complete l_1,...,l_r to a basis of the non-x degree-one space. Adding the next basis form z to a square-zero cut preserves square-zero H0. Multiplication by z on the old H0 has rank exactly one: it sends the unit to its independent nonzero linear class and kills all positive-degree elements.

The exact Koszul cone identity is basis-independent. If C(u)=sum c_j u^j and rho_j is multiplication rank on the actual old Koszul H_j, then

    C_new=(1+u)C_old-sum rho_j u^j,
    c'_j=c_j+c_(j-1)-rho_j,
    rho_0=1.

The target coefficients satisfy the same pure combinatorial recurrence as in the inherited actual-variable proof:

    R'_1=R_1+c_0,  R'_j=R_j+R_(j-1) (j>=2).

Thus every paid rank budget stays paid while completing the linear basis. At the full cut the Koszul complex is related to the original full complex by an invertible linear coordinate change, so its Betti numbers are the intrinsic beta_i(G). The target is the same ordinary T_m and is independent of this basis. The final full-cut coefficient comparison is exactly the R54 ordinary-target comparison. This proves the required basis-free payment conclusion without assuming numerical-coordinate behavior for the new forms.

## 5. Green's exact quadratic iteration

Pass first to an infinite field extension if needed. Flat scalar extension preserves all intrinsic Betti dimensions, the actual source/target, and the numerical tower lengths. Any proof of the Betti inequality over that extension therefore proves it over the original field.

Let n=e-1. Write the actual quadratic dimension uniquely as

    a=C(p+1,2)+b,  0<=b<=p.

For a=0 take p=b=0. Since a<=C(n+1,2), one has p<=n. Green's degree-two bound for one general hyperplane is

    dim(A/(l))2 <= C(p,2)+max(b-1,0).

This is the usual degree-two binomial lowering, obtained from the lex quadratic standards after deleting the last variable. The bound is monotone in a. Inductively, after s general independent forms, for 0<=s<=p,

    dim(A/(l_1,...,l_s))2
         <= C(p+1-s,2)+max(b-s,0).                        (3)

The binomial expansion stays valid at every step because its second index b-s is strictly below p+1-s when it is positive. At s=p, both terms vanish. A standard graded algebra with zero degree-two piece has every higher piece zero. Therefore p general independent non-x forms give a square-zero quotient.

If p<3, extend them to three independent forms, possible because e>=4. Hence there is a square-zero linear cut of size r(a)=max(3,p(a)). Its size is at most e-1. Sections3–4 and the all-rank harmonic chamber prove (1).

## 6. Head dimension twenty and defect twenty

If a<=20, then p(a)<=5, because C(7,2)=21. Thus r(a)<=5 and

    H(r(a))<=H(5)=273.

For every source outside the accepted E273/D16 inherited closures,

    e>=274,  d>=17,
    2e+d>=565>273.

Condition(1) applies and pays all P14 rows. Sources inside either inherited closure are paid by that explicitly named dependency. This proves the head-dimension20 statement. Since a<=d, it implies ordinary P14 for every d<=20.

This reasoning does not assert that these sources possess an actual numerical hitting set of size five. The generic linear cut is exactly the new extension, and its Betti payment is justified by Sections3–4.

## 7. The fixed-defect tail

Monotonicity gives p(a)<=p(d) and r(a)<=r_d. Since H(r) increases, (2) implies (1). An explicit integer embedding-dimension threshold is

    e >= max(4, ceil((H(r_d)-d)/2)).

For fixed d, the required r_d is O(sqrt(d)). The exact central binomial coefficient in H then gives H(r_d)=exp(O(sqrt(d))). More precisely, as d tends to infinity,

    p(d)=sqrt(2d)+O(1),
    log H(r_d)=sqrt(2d)*log4+O(log d).

The O(1) ambiguity from the triangular intervals is absorbed in the logarithmic remainder. No exact asymptotic equivalent with a single constant is claimed across the jumps of p(d).

For comparison only, the inherited R55 coarse tail used P=min{q:C(q+1,2)>=d} and e of order (P*d)^(P-1), whose logarithm is O(sqrt(d) log d). Both are sufficient chambers, and neither proves global closure when d,e grow outside them.
