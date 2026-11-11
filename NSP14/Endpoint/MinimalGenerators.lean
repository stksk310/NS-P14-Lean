module
public import NSP14.Endpoint.Residues
public import NSP14.Endpoint.FiberIndices
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open scoped Classical
namespace NSP14.Endpoint.Data
variable (D : NSP14.Endpoint.Data)

noncomputable def minimalPoints (r : Fin D.u) : Finset (ℕ×ℕ) := (D.minimalFiber_finite r).toFinset

@[simp] theorem mem_minimalPoints (r : Fin D.u) (c : ℕ×ℕ) :
    c∈D.minimalPoints r ↔ Minimal (·∈D.coreFiber r) c := Set.Finite.mem_toFinset _

noncomputable def coreHeight : ℕ := Finset.univ.sup (fun r : Fin D.u => (D.minimalPoints r).sup Prod.fst)

theorem minimalPoint_height (r : Fin D.u) (c : ℕ×ℕ) (hc : c∈D.minimalPoints r) : c.1≤D.coreHeight :=
  (Finset.le_sup hc).trans (Finset.le_sup (f:=fun r : Fin D.u => (D.minimalPoints r).sup Prod.fst) (Finset.mem_univ r))

theorem coreHeight_le : D.coreHeight≤D.u-2 := by
  apply Finset.sup_le
  intro r _
  apply Finset.sup_le
  intro c hc
  have h := D.minimalFiber_budget r c ((D.mem_minimalPoints r c).mp hc)
  omega

variable (k : Type) [Field k]

/-- The actual ideal has precisely the minimal bounded internal words
as monomial generators. This is stronger than abstract Noetherianity. -/
theorem coreFiberIdeal_minimal_generators (r : Fin D.u) :
    D.coreFiberIdeal k r=Ideal.span ((fun β : Fin 2 →₀ ℕ => MvPolynomial.monomial β (1:k)) ''
      {β | Minimal (·∈D.coreFiber r) (β 0,β 1)}) := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro _ ⟨β,hβ,rfl⟩
    apply MvPolynomial.mem_ideal_span_monomial_image.mpr
    intro γ hγ
    have he : β=γ := by
      by_contra hne
      have hz : (MvPolynomial.monomial β (1:k)).coeff γ=0 := by
        simp only [MvPolynomial.coeff_monomial,hne,ite_false]
      exact (Finsupp.mem_support_iff.mp hγ) hz
    subst γ
    obtain ⟨c,hc,hmin⟩ := D.exists_minimalFiber_le r (β 0,β 1) hβ
    refine ⟨NSP14.Endpoint.exponentPairEquiv c,?_,?_⟩
    · change Minimal (·∈D.coreFiber r) (NSP14.Endpoint.exponentPairEquiv.symm (NSP14.Endpoint.exponentPairEquiv c))
      rw [AddEquiv.symm_apply_apply]
      exact hmin
    · intro i
      fin_cases i <;> simpa [NSP14.Endpoint.exponentPairEquiv] using (by first | exact hc.1 | exact hc.2)
  · apply Ideal.span_le.mpr
    rintro _ ⟨β,hβ,rfl⟩
    exact Ideal.subset_span ⟨β,hβ.prop,rfl⟩

theorem coreFiberIdeal_ne_bot (r : Fin D.u) : D.coreFiberIdeal k r≠⊥ := by
  obtain ⟨c,hc⟩ := D.coreFiber_nonempty r
  let β := NSP14.Endpoint.exponentPairEquiv c
  have hβ : (β 0,β 1)∈D.coreFiber r := by
    change NSP14.Endpoint.exponentPairEquiv.symm (NSP14.Endpoint.exponentPairEquiv c)∈D.coreFiber r
    rw [AddEquiv.symm_apply_apply]
    exact hc
  have hm : MvPolynomial.monomial β (1:k)∈D.coreFiberIdeal k r := Ideal.subset_span ⟨β,hβ,rfl⟩
  intro hz
  rw [hz,Submodule.mem_bot] at hm
  have hcoeff := congrArg (fun f : D.EndpointRing k => f.coeff β) hm
  exact one_ne_zero (by simpa only [MvPolynomial.coeff_monomial,ite_true,AddMonoidAlgebra.coeff_zero,Finsupp.zero_apply] using hcoeff)
end NSP14.Endpoint.Data
