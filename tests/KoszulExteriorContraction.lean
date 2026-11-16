module
public import NSP14.Homological.KoszulExteriorBasis
@[expose] public section
open scoped Classical BigOperators
namespace NSP14.Tests.KoszulExteriorContraction
theorem actual_basis_signed_contraction (k σ : Type) [Field k] [Fintype σ]
    (φ : Module.Dual k (σ → k)) (j : ℕ)
    (s : Homological.KoszulSlot (Homological.variableList k σ).length (j+1)) :
    CliffordAlgebra.contractLeft φ
      (Homological.koszulExteriorBasis (σ:=σ) k (j+1) s : ExteriorAlgebra k (σ → k)) =
      ∑ t : Homological.KoszulSlot (Homological.variableList k σ).length j,
        Homological.koszulArrowScalar k (fun x : σ => Pi.single x 1) φ
          (Homological.koszulSlotArrow (Homological.variableList k σ) j s t) •
            (Homological.koszulExteriorBasis (σ:=σ) k j t : ExteriorAlgebra k (σ → k)) := by
  simp_rw [Homological.koszulExteriorBasis_apply,Homological.koszulSlotExterior_coe]
  exact Homological.koszulSlotWord_contraction k _ φ _ j s
end NSP14.Tests.KoszulExteriorContraction
