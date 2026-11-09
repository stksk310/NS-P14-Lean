# A universal defect bound on every terminal jump

This is an unconditional numerical-coordinate consequence of the R55
Apéry ideal and opposite-jump theorem. It does not prove a linear bound
on the number of relative terminal generators.

Let `G` be any genuine numerical semigroup tangent cone, with actual
multiplicity variable `x=[m]`, embedding dimension `e`, and
`delta=m-e`. Use the actual polynomial ring `S` on the `e-1` non-x
variables. Write

\[
 A=G/xG,\qquad T=(0:_Gx),\qquad
 N=\langle\hbox{non-Apéry x-head coordinates}\rangle\subset A,
 \qquad Q=A/N.
\]

The companion nonflat theorem proves that `N` is a genuine coordinate
ideal, that `Q` has numerical Apéry basis, and that `length Q=m`.
Let

\[
 \nu=\max\{j:Q_j\ne0\}.
\]

For each actual finite x-string terminal `tau`, put

\[
 d(\tau)=\operatorname{ord}(\tau+m)-\operatorname{ord}(\tau).
\]

**Theorem.** If `T` is nonzero, then

\[
 \boxed{2\le d(\tau)\le\nu\le\delta+1
           \quad\hbox{for every terminal }\tau.}\tag{1}
\]

Consequently the common jump filtration has at most `nu-1<=delta`
nonzero strata, and `nu<=1` forces `T=0`.

**Proof.** The algebra `Q` is standard graded of actual embedding
dimension `e-1`, so its degree-zero and degree-one pieces have total
length `e`. It has exactly `delta` nonlinear coordinate basis elements.
If `Q_nu` is nonzero with `nu>=2`, standard generation implies
`Q_j` is nonzero for each `2<=j<=nu`. Thus
`delta>=nu-1`, proving the final inequality.

Write `A=S/I_A`, `Q=S/I_Q`; then `I_A` is contained in `I_Q`, and
`N=I_Q/I_A`. Since `Q_(nu+1)=0`, every monomial of degree `nu+1` lies
in `I_Q`. Hence `I_Q` is generated in degrees at most `nu+1` (truncate
any homogeneous generating set at that degree; higher-degree
monomials are multiples of the degree-`nu+1` monomials). The quotient
module `N` is therefore generated in degrees at most `nu+1` as well.

The coordinate action makes `S_+N` a coordinate span. Accordingly,
one may choose the minimal generators of `N` to be its coordinate
heads outside that span. Each such head `alpha` has degree at most
`nu+1` and, by the terminal/head basis bijection, has the form
`alpha=tau+m` for a positive terminal `tau`. Positivity gives
`ord(tau)>=1`; therefore

\[
 d(\tau)=\deg(alpha)-\operatorname{ord}(\tau)
            \le\nu.
\]

Every coordinate of `N` is obtained from a minimal coordinate generator
by a live product of actual non-x variables. Indeed the coordinate
generators span `N` under monomial action, and every nonzero product is
again one coordinate; any target coordinate in their span must occur
as one such nonzero product. Along a live `N` arrow the terminal jump
is nonincreasing, by the companion opposite-jump theorem. The same
bound therefore propagates from the minimal coordinate heads to all
of `N`, hence to every terminal. The lower bound two is exactly the
definition of a dead x-arrow with existing predecessor. All arguments
are integral coordinate statements and remain valid over every field.
QED.

## Relation to the rank-payment problem

The theorem gives a finite jump range independent of the largest atom,
genus, or normalized offset width. In particular, at fixed defect,
unbounded actual atoms cannot create arbitrarily many different jump
values. It complements the exact r2 field-independent formula

\[
 c_1=|S_A|+|B_T|-\rho,\qquad c_2=|S_T|.
\]

It does not bound the sizes of the individual strata or the number of
minimal y,z-generators in them. The number of strata alone cannot be
substituted for a bound on `|B_T|`, and it does not justify the false
module domination `mu(T)<=mu(N)`.

The genuine source `<32,45,307>` has terminal jumps `6,15,24` and
defect `29`, illustrating that jumps may exceed two while satisfying
(1). The universal statement is the bound, not constancy of the jump.

Dependencies: the canonical Apéry ideal/basis bijection and the
nonincreasing jump rule on live N-arrows, both proved in
`nonflat_socle/APERY_QUOTIENT_SOCLE_TORSION_FUSION.md` and
`nonflat_socle/OPPOSITE_JUMP_FILTRATIONS_AND_COMMON_STRATA.md`.
