module
public import Mathlib.LinearAlgebra.Vandermonde
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
@[expose] public section
open scoped BigOperators Classical
namespace NSP14.Homological
variable (k : Type*) [Field k] {I : Type*} [Fintype I]

/-- Polynomial evaluation functionals and moment image vectors have
independent rows on every set of no more points than coordinates. -/
theorem momentVectors_independent {d : ℕ} (t : I → k) (ht : Function.Injective t)
    (hd : Fintype.card I ≤ d) :
    LinearIndependent k (fun i => (fun a : Fin d => t i^a.val)) := by
  apply Fintype.linearIndependent_iff.mpr
  intro c hc i
  let e := Fintype.equivFin I
  have hz : (fun a : Fin (Fintype.card I) => c (e.symm a))=0 := by
    apply Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero (ht.comp e.symm.injective)
    intro j
    have he := congrFun hc (Fin.castLE hd j)
    simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,Fin.val_castLE,Pi.zero_apply] at he
    exact (e.symm.sum_comp (fun a => c a*t a^j.val)).trans he
  have he := congrFun hz (e i)
  simpa only [Equiv.symm_apply_apply,Pi.zero_apply] using he

noncomputable def momentFunctional (d : ℕ) (t : k) : (Fin d → k) →ₗ[k] k :=
  Fintype.linearCombination k (fun a : Fin d => t^a.val)

theorem momentFunctional_independent {d : ℕ} (t : I → k) (ht : Function.Injective t)
    (hd : Fintype.card I ≤ d) :
    LinearIndependent k (fun i => momentFunctional k d (t i)) := by
  have hi := momentVectors_independent k t ht hd
  apply Fintype.linearIndependent_iff.mpr
  intro c hc i
  apply (Fintype.linearIndependent_iff.mp hi) c ?_ i
  funext a
  have he := LinearMap.congr_fun hc (Pi.single a 1)
  simpa [momentFunctional,Fintype.linearCombination_apply,Pi.single_apply] using he

/-- At least d distinct evaluation points separate polynomials represented
by their d coefficients. No assumption on the characteristic is used. -/
theorem momentFunctional_separate {d : ℕ} (t : I → k) (ht : Function.Injective t)
    (hd : d ≤ Fintype.card I) (c : Fin d → k)
    (hc : ∀ i,momentFunctional k d (t i) c=0) : c=0 := by
  let f : Fin d ↪ I := (Function.Embedding.truncOfCardLE (by simpa using hd)).out
  apply Matrix.eq_zero_of_forall_index_sum_mul_pow_eq_zero (ht.comp f.injective)
  intro i
  exact hc (f i)

/-- Dually, the same moment vectors span once there are at least d
points. We state the separation property needed for the actual dual map. -/
theorem momentVectors_dual_separate {d : ℕ} (t : I → k) (ht : Function.Injective t)
    (hd : d ≤ Fintype.card I) (f : (Fin d → k) →ₗ[k] k)
    (hf : ∀ i,f (fun a => t i^a.val)=0) : f=0 := by
  let c : Fin d → k := fun a => f (Pi.single a 1)
  have hc : c=0 := by
    apply momentFunctional_separate k t ht hd
    intro i
    have h : (∑ a : Fin d,t i^a.val • Pi.single a 1)=(fun a : Fin d => t i^a.val) := by
      ext a
      simp [Pi.single_apply]
    have he := congrArg f h
    rw [map_sum] at he
    simp only [map_smul,smul_eq_mul] at he
    change ∑ a : Fin d,c a*t i^a.val=0
    simpa only [mul_comm] using he.trans (hf i)
  apply LinearMap.ext
  intro v
  have h : (∑ a : Fin d,v a • Pi.single a 1)=v := by ext a;simp [Pi.single_apply]
  rw [← h,map_sum]
  apply Finset.sum_eq_zero
  intro a _
  rw [map_smul]
  have hz := congrFun hc a
  change f (Pi.single a 1)=0 at hz
  simp [hz]
end NSP14.Homological
