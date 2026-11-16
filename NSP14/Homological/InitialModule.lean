module
public import NSP14.Homological.OrderedQuotientBasis
public import Mathlib.RingTheory.MvPolynomial.MonomialOrder
public import Mathlib.Order.Prod.Lex.Basic
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
@[expose] public section
open scoped Classical BigOperators
namespace NSP14.Homological
variable (k : Type*) {σ M : Type*} [Field k] [AddCommGroup M] [Module k M]
  [Module (MvPolynomial σ k) M] [IsScalarTower k (MvPolynomial σ k) M]
  (m : MonomialOrder σ) {q : ℕ} (g : Fin q → M)

abbrev ModuleTerm := m.syn ×ₗ Fin q

noncomputable def moduleTermVector (i : ModuleTerm m (q:=q)) : M :=
  (MvPolynomial.monomial (m.toSyn.symm (ofLex i).1) (1:k)) • g (ofLex i).2

noncomputable def moduleTermShift (d : σ →₀ ℕ) (i : ModuleTerm m (q:=q)) : ModuleTerm m (q:=q) :=
  toLex ((ofLex i).1+m.toSyn d,(ofLex i).2)

theorem moduleTermShift_strictMono (d : σ →₀ ℕ) : StrictMono (moduleTermShift m (q:=q) d) := by
  intro a b hab
  rw [Prod.Lex.lt_iff] at hab ⊢
  simp only [moduleTermShift,ofLex_toLex]
  rcases hab with h|⟨h,h'⟩
  · apply Or.inl
    simpa only [add_comm] using add_lt_add_right h (m.toSyn d)
  · exact Or.inr ⟨congrArg (fun x => x+m.toSyn d) h,h'⟩

omit [Module k M] [IsScalarTower k (MvPolynomial σ k) M] in
theorem moduleTermVector_shift (d : σ →₀ ℕ) (i : ModuleTerm m (q:=q)) :
    moduleTermVector k m g (moduleTermShift m d i)=
      (MvPolynomial.monomial d (1:k)) • moduleTermVector k m g i := by
  simp only [moduleTermVector,moduleTermShift,ofLex_toLex,map_add,AddEquiv.symm_apply_apply]
  rw [smul_smul,MvPolynomial.monomial_mul_monomial,one_mul,add_comm]

/-- The actual P-generating set gives the required coefficient-space span.
This includes arbitrary q and does not identify a module kernel with an ideal. -/
theorem moduleTermVector_span (hg : Submodule.span (MvPolynomial σ k) (Set.range g)=⊤) :
    Submodule.span k (Set.range (moduleTermVector k m g))=⊤ := by
  let U := Submodule.span k (Set.range (moduleTermVector k m g))
  have hp : ∀ (p : MvPolynomial σ k) (l : Fin q),p • g l ∈ U := by
    intro p l
    rw [p.as_sum,Finset.sum_smul]
    apply U.sum_mem
    intro d _
    have h : (MvPolynomial.monomial d (1:k)) • g l ∈ U := by
      exact Submodule.subset_span ⟨toLex (m.toSyn d,l),by
        simp only [moduleTermVector,ofLex_toLex,AddEquiv.symm_apply_apply]⟩
    have h' := U.smul_mem (p.coeff d) h
    rw [← smul_assoc,MvPolynomial.smul_monomial,smul_eq_mul,mul_one] at h'
    exact h'
  apply top_unique
  intro a _
  have ha : a ∈ Submodule.span (MvPolynomial σ k) (Set.range g) := by rw [hg];trivial
  obtain ⟨c,hc⟩ := (Submodule.mem_span_range_iff_exists_fun (MvPolynomial σ k)).mp ha
  rw [← hc]
  exact U.sum_mem (fun l _ => hp (c l) l)

/-- The standard labels of the actual module presentation P^q -> M. -/
noncomputable def ModuleStandard : Set (ModuleTerm m (q:=q)) :=
  OrderedStandards k (moduleTermVector k m g)

noncomputable def moduleStandardBasis (hg : Submodule.span (MvPolynomial σ k) (Set.range g)=⊤) :
    Module.Basis (ModuleStandard k m g) k M :=
  orderedStandardBasis k (moduleTermVector k m g) (moduleTermVector_span k m g hg)

theorem moduleStandardBasis_apply (hg : Submodule.span (MvPolynomial σ k) (Set.range g)=⊤)
    (i : ModuleStandard k m g) : moduleStandardBasis k m g hg i=moduleTermVector k m g i.val :=
  orderedStandardBasis_apply k _ _ i

/-- Actual divisor closure, in the same generator component. -/
theorem moduleStandard_divisor (d : σ →₀ ℕ) (i : ModuleTerm m (q:=q))
    (hi : moduleTermShift m d i ∈ ModuleStandard k m g) : i ∈ ModuleStandard k m g := by
  let T : M →ₗ[k] M :=
    { toFun a := (MvPolynomial.monomial d (1:k)) • a
      map_add' _ _ := smul_add _ _ _
      map_smul' c a := smul_comm _ _ _ }
  exact orderedStandards_shift_down k (moduleTermVector k m g) T (moduleTermShift m d)
    (moduleTermShift_strictMono m d) (fun j => (moduleTermVector_shift k m g d j).symm) i hi

/-- Actual multiplication cannot create a larger module term in standard
coordinates. This is the triangular statement needed for Koszul minors. -/
theorem moduleStandardBasis_shift_coeff_zero (hg : Submodule.span (MvPolynomial σ k) (Set.range g)=⊤)
    (d : σ →₀ ℕ) (i j : ModuleStandard k m g) (hji : moduleTermShift m d i.val < j.val) :
    (moduleStandardBasis k m g hg).repr ((MvPolynomial.monomial d (1:k)) • moduleStandardBasis k m g hg i) j=0 := by
  rw [moduleStandardBasis_apply,← moduleTermVector_shift]
  exact orderedStandardBasis_repr_zero_above k _ _ _ j hji

theorem moduleStandard_finite [Module.Finite k M]
    (hg : Submodule.span (MvPolynomial σ k) (Set.range g)=⊤) : Finite (ModuleStandard k m g) :=
  (moduleStandardBasis k m g hg).linearIndependent.finite
end NSP14.Homological
