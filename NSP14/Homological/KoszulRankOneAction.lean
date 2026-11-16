module
public import NSP14.Homological.KoszulCoefficientSlots
public import NSP14.Homological.FiniteKoszulEuler
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory
open scoped Classical BigOperators
namespace NSP14.Homological
universe u
variable (k σ : Type u) [Field k] (M : ModuleCat.{u} (VariableRing k σ))
  (u₀ : coefficientModule k σ M) (ℓ : coefficientModule k σ M →ₗ[k] k)
  (hact : ∀ v (a : coefficientModule k σ M),
    (MvPolynomial.X v : VariableRing k σ) • a=ℓ a • ((MvPolynomial.X v : VariableRing k σ) • u₀))

include hact in
theorem koszulSignedVariable_rankOne (o : Option (σ × Bool)) (a : coefficientModule k σ M) :
    (show coefficientModule k σ M from (koszulSignedVariable k σ M o).hom a)=
      ℓ a • (show coefficientModule k σ M from (koszulSignedVariable k σ M o).hom u₀) := by
  cases o with
  | none => simp [koszulSignedVariable]
  | some p =>
    rcases p with ⟨v,b⟩
    cases b with
    | false => exact hact v a
    | true =>
      change -((MvPolynomial.X v : VariableRing k σ) • a)=ℓ a • -((MvPolynomial.X v : VariableRing k σ) • u₀)
      rw [hact,smul_neg]

include hact in
theorem coefficientColumn_d_factor (xs : List σ) (j : ℕ)
    (s : KoszulSlot xs.length (j+1)) (a : coefficientModule k σ M) :
    ((coefficientKoszulListFunctor k σ xs).obj M).d (j+1) j (coefficientSlotIn k σ M xs (j+1) s a)=
      ℓ a • ((coefficientKoszulListFunctor k σ xs).obj M).d (j+1) j (coefficientSlotIn k σ M xs (j+1) s u₀) := by
  apply coefficientSlotOut_ext k σ M xs j
  intro t
  rw [map_smul,coefficientSlot_d_arrow,coefficientSlot_d_arrow]
  exact koszulSignedVariable_rankOne k σ M u₀ ℓ hact _ a

include hact in
theorem coefficient_d_rankOne_span (xs : List σ) (j : ℕ)
    (a : ((coefficientKoszulListFunctor k σ xs).obj M).X (j+1)) :
    ((coefficientKoszulListFunctor k σ xs).obj M).d (j+1) j a ∈
      Submodule.span k (Set.range (fun s : KoszulSlot xs.length (j+1) =>
        ((coefficientKoszulListFunctor k σ xs).obj M).d (j+1) j (coefficientSlotIn k σ M xs (j+1) s u₀))) := by
  have he := coefficientSlot_decompose k σ M xs (j+1) a
  rw [he,map_sum]
  apply Submodule.sum_mem
  intro s _
  rw [coefficientColumn_d_factor k σ M u₀ ℓ hact]
  apply Submodule.smul_mem
  exact Submodule.subset_span (Set.mem_range_self s)

include hact in
theorem coefficient_d_rankOne_rank_le [Module.Finite k (coefficientModule k σ M)]
    (xs : List σ) (j : ℕ) :
    Module.finrank k (((coefficientKoszulListFunctor k σ xs).obj M).d (j+1) j).hom.range ≤ xs.length.choose (j+1) := by
  let : Module.Finite k (((coefficientKoszulListFunctor k σ xs).obj M).X j) :=
    koszul_chain_coefficient_finite k σ xs M j
  let v : KoszulSlot xs.length (j+1) → ((coefficientKoszulListFunctor k σ xs).obj M).X j :=
    fun s => ((coefficientKoszulListFunctor k σ xs).obj M).d (j+1) j (coefficientSlotIn k σ M xs (j+1) s u₀)
  have hr : (((coefficientKoszulListFunctor k σ xs).obj M).d (j+1) j).hom.range ≤
      Submodule.span k (Set.range v) := by
    rintro _ ⟨a,rfl⟩
    exact coefficient_d_rankOne_span k σ M u₀ ℓ hact xs j a
  exact (Submodule.finrank_mono hr).trans ((finrank_range_le_card v).trans_eq (koszulSlot_card _ _))
end NSP14.Homological
