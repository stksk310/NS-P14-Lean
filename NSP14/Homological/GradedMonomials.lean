module
public import NSP14.Homological.GradedBasis
public import NSP14.Homological.InitialModule
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory
open scoped Classical
namespace NSP14.Homological
universe u
variable (k σ : Type u) [Field k] (M : ModuleCat.{u} (VariableRing k σ))
  (G : GradedPolynomialModule k σ M)

/-- The grading of a monomial action is obtained from the actual variable
maps, rather than added as a homogeneous-presentation assumption. -/
theorem graded_monomial_mem (d : σ →₀ ℕ) (q : ℤ) (a : coefficientModule k σ M)
    (ha : a ∈ G.degreeSpace q) :
    (MvPolynomial.monomial d (1:k)) • a ∈ G.degreeSpace (q+d.degree) := by
  revert q a
  induction d using Finsupp.induction_linear with
  | zero =>
    intro q a ha
    simpa only [map_zero,Nat.cast_zero,add_zero,MvPolynomial.monomial_zero',
      MvPolynomial.C_1,one_smul] using ha
  | add d e hd he =>
    intro q a ha
    have h := hd (q+e.degree) ((MvPolynomial.monomial e (1:k)) • a) (he q a ha)
    rw [smul_smul,MvPolynomial.monomial_mul_monomial,one_mul] at h
    simpa only [map_add,Nat.cast_add,add_comm,add_left_comm,add_assoc] using h
  | single x n =>
    induction n with
    | zero =>
      intro q a ha
      simpa only [Finsupp.single_zero,map_zero,Nat.cast_zero,add_zero,
        MvPolynomial.monomial_zero',MvPolynomial.C_1,one_smul] using ha
    | succ n ih =>
      intro q a ha
      have hn := ih q a ha
      simp only [Finsupp.degree_single] at hn
      have h := G.variable_mem (q+n) x hn
      have hm : (MvPolynomial.monomial (Finsupp.single x (n+1)) (1:k))=
          MvPolynomial.X x*MvPolynomial.monomial (Finsupp.single x n) (1:k) := by
        simp only [← MvPolynomial.X_pow_eq_monomial,pow_succ']
      rw [hm,mul_smul]
      simpa only [Finsupp.degree_single,Nat.cast_add,Nat.cast_one,add_assoc] using h

variable (m : MonomialOrder σ) {r : ℕ} (g : Fin r → coefficientModule k σ M)
  (b : ℤ) (hg : Submodule.span (VariableRing k σ) (Set.range g)=⊤)
  (hdeg : ∀ i,g i ∈ G.degreeSpace b)

include hdeg in
theorem moduleTermVector_homogeneous (i : ModuleTerm m (q:=r)) :
    moduleTermVector k m g i ∈ G.degreeSpace (b+(m.toSyn.symm (ofLex i).1).degree) :=
  graded_monomial_mem k σ M G _ b _ (hdeg _)

include hdeg in
theorem moduleStandardBasis_homogeneous (i : ModuleStandard k m g) :
    moduleStandardBasis k m g hg i ∈ G.degreeSpace (b+(m.toSyn.symm (ofLex i.val).1).degree) := by
  rw [moduleStandardBasis_apply]
  exact moduleTermVector_homogeneous k σ M G m g b hdeg i.val

include hg hdeg in
theorem moduleStandardBasis_degree_count [Module.Finite k (coefficientModule k σ M)] (t : ℕ) :
    Module.finrank k (G.piece (b+t))=
      Nat.card {i : ModuleStandard k m g // b+(m.toSyn.symm (ofLex i.val).1).degree=b+t} :=
  gradedBasis_piece_finrank k σ M G (moduleStandardBasis k m g hg)
    (fun i => b+(m.toSyn.symm (ofLex i.val).1).degree)
    (moduleStandardBasis_homogeneous k σ M G m g b hg hdeg) _
end NSP14.Homological
