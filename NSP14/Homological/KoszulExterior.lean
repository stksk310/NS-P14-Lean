module
public import NSP14.Homological.KoszulExteriorBasis
public import NSP14.Homological.KoszulSlotGrading
public import Mathlib.LinearAlgebra.TensorProduct.Basis
@[expose] public section
open scoped Classical TensorProduct BigOperators
open CategoryTheory
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace NSP14.Homological
variable (k σ : Type) [Field k] [Fintype σ]

def koszulExteriorContraction (j : ℕ) (φ : Module.Dual k (σ → k)) :
    (⋀[k]^(j+1) (σ → k)) →ₗ[k] (⋀[k]^j (σ → k)) :=
  (koszulExteriorBasis (σ:=σ) k (j+1)).constr k (fun s =>
    ∑ t : KoszulSlot (variableList k σ).length j,
      koszulArrowScalar k (fun x : σ => Pi.single x 1) φ
        (koszulSlotArrow (variableList k σ) j s t) • koszulExteriorBasis (σ:=σ) k j t)

theorem koszulExteriorContraction_basis (j : ℕ) (φ : Module.Dual k (σ → k))
    (s : KoszulSlot (variableList k σ).length (j+1)) :
    koszulExteriorContraction k σ j φ (koszulExteriorBasis (σ:=σ) k (j+1) s)=
      ∑ t : KoszulSlot (variableList k σ).length j,
        koszulArrowScalar k (fun x : σ => Pi.single x 1) φ
          (koszulSlotArrow (variableList k σ) j s t) • koszulExteriorBasis (σ:=σ) k j t :=
  Module.Basis.constr_basis _ _ _ _

theorem koszulExteriorContraction_coe (j : ℕ) (φ : Module.Dual k (σ → k))
    (w : ⋀[k]^(j+1) (σ → k)) :
    (koszulExteriorContraction k σ j φ w : ExteriorAlgebra k (σ → k))=
      CliffordAlgebra.contractLeft φ w.val := by
  have h : (Submodule.subtype (⋀[k]^j (σ → k))).comp (koszulExteriorContraction k σ j φ)=
      (CliffordAlgebra.contractLeft φ).comp (Submodule.subtype (⋀[k]^(j+1) (σ → k))) := by
    apply (koszulExteriorBasis (σ:=σ) k (j+1)).ext
    intro s
    simp only [LinearMap.comp_apply,koszulExteriorContraction_basis,map_sum,map_smul]
    change (∑ t, koszulArrowScalar k (fun x : σ => Pi.single x 1) φ
      (koszulSlotArrow (variableList k σ) j s t) •
        (koszulExteriorBasis (σ:=σ) k j t : ExteriorAlgebra k (σ → k)))=
        CliffordAlgebra.contractLeft φ (koszulExteriorBasis (σ:=σ) k (j+1) s : ExteriorAlgebra k (σ → k))
    simp_rw [koszulExteriorBasis_apply,koszulSlotExterior_coe]
    exact (koszulSlotWord_contraction k _ φ _ j s).symm
  exact LinearMap.congr_fun h w

variable (M : ModuleCat (VariableRing k σ)) {J : Type}
  (b : Module.Basis J k (coefficientModule k σ M))

def koszulExteriorTensorEquiv (j : ℕ) :
    coefficientModule k σ ((koszulList k σ (variableList k σ) M).X j) ≃ₗ[k]
      coefficientModule k σ M ⊗[k] (⋀[k]^j (σ → k)) :=
  (koszulSlotBasis k σ M b (variableList k σ) j).equiv
    (b.tensorProduct (koszulExteriorBasis (σ:=σ) k j)) (Equiv.prodComm _ _)

theorem koszulExteriorTensorEquiv_basis (j : ℕ)
    (s : KoszulSlot (variableList k σ).length j) (a : J) :
    koszulExteriorTensorEquiv k σ M b j
      (koszulSlotBasis k σ M b (variableList k σ) j (s,a))=
      b a ⊗ₜ[k] koszulExteriorBasis (σ:=σ) k j s := by
  rw [koszulExteriorTensorEquiv,Module.Basis.equiv_apply,Module.Basis.tensorProduct_apply]
  rfl

theorem koszulExteriorTensorEquiv_slot (j : ℕ)
    (s : KoszulSlot (variableList k σ).length j) (a : coefficientModule k σ M) :
    koszulExteriorTensorEquiv k σ M b j (coefficientSlotIn k σ M (variableList k σ) j s a)=
      a ⊗ₜ[k] koszulExteriorBasis (σ:=σ) k j s := by
  have h : (koszulExteriorTensorEquiv k σ M b j).toLinearMap.comp
      (coefficientSlotIn k σ M (variableList k σ) j s)=
    (TensorProduct.mk k (coefficientModule k σ M) (⋀[k]^j (σ → k))).flip
      (koszulExteriorBasis (σ:=σ) k j s) := by
    apply b.ext
    intro a
    change koszulExteriorTensorEquiv k σ M b j
      (coefficientSlotIn k σ M (variableList k σ) j s (b a))=_
    rw [← koszulSlotBasis_apply,koszulExteriorTensorEquiv_basis]
    rfl
  exact LinearMap.congr_fun h a

theorem koszulExteriorTensorEquiv_boundary_slot (j : ℕ)
    (s : KoszulSlot (variableList k σ).length (j+1)) (a : coefficientModule k σ M) :
    koszulExteriorTensorEquiv k σ M b j
      (((coefficientKoszulListFunctor k σ (variableList k σ)).obj M).d (j+1) j
        (coefficientSlotIn k σ M (variableList k σ) (j+1) s a)) =
      ∑ t : KoszulSlot (variableList k σ).length j,
        (show coefficientModule k σ M from
          (koszulSignedVariable k σ M (koszulSlotArrow (variableList k σ) j s t)).hom a) ⊗ₜ[k]
          koszulExteriorBasis (σ:=σ) k j t := by
  have h := congrArg (koszulExteriorTensorEquiv k σ M b j)
    (coefficientSlot_decompose k σ M (variableList k σ) j
      (((coefficientKoszulListFunctor k σ (variableList k σ)).obj M).d (j+1) j
        (coefficientSlotIn k σ M (variableList k σ) (j+1) s a)))
  simpa only [map_sum,koszulExteriorTensorEquiv_slot,coefficientSlot_d_arrow] using h

theorem koszulSignedVariable_sum_coords (e : Option (σ × Bool)) (a : coefficientModule k σ M) :
    (show coefficientModule k σ M from (koszulSignedVariable k σ M e).hom a)=
      ∑ x : σ,koszulArrowScalar k (fun x : σ => Pi.single x (1:k)) (LinearMap.proj x) e •
        ((MvPolynomial.X x : VariableRing k σ) • a) := by
  cases e with
  | none => simp [koszulSignedVariable,koszulArrowScalar]
  | some e => rcases e with ⟨x,sign⟩; cases sign <;>
    simp [koszulSignedVariable,koszulArrowScalar,Pi.single_apply,neg_smul]

theorem koszulExteriorTensorEquiv_boundary_contraction_slot (j : ℕ)
    (s : KoszulSlot (variableList k σ).length (j+1)) (a : coefficientModule k σ M) :
    koszulExteriorTensorEquiv k σ M b j
      (((coefficientKoszulListFunctor k σ (variableList k σ)).obj M).d (j+1) j
        (coefficientSlotIn k σ M (variableList k σ) (j+1) s a)) =
      ∑ x : σ,((MvPolynomial.X x : VariableRing k σ) • a) ⊗ₜ[k]
        koszulExteriorContraction k σ j (LinearMap.proj x)
          (koszulExteriorBasis (σ:=σ) k (j+1) s) := by
  rw [koszulExteriorTensorEquiv_boundary_slot]
  simp_rw [koszulSignedVariable_sum_coords,TensorProduct.sum_tmul]
  rw [Finset.sum_comm]
  simp_rw [koszulExteriorContraction_basis,TensorProduct.tmul_sum,TensorProduct.tmul_smul]
  rfl

def koszulExteriorBoundary (j : ℕ) :
    (coefficientModule k σ M ⊗[k] (⋀[k]^(j+1) (σ → k))) →ₗ[k]
      coefficientModule k σ M ⊗[k] (⋀[k]^j (σ → k)) :=
  (koszulExteriorTensorEquiv k σ M b j).toLinearMap.comp
    ((((coefficientKoszulListFunctor k σ (variableList k σ)).obj M).d (j+1) j).hom.comp
      (koszulExteriorTensorEquiv k σ M b (j+1)).symm.toLinearMap)

theorem koszulExteriorBoundary_tmul_basis (j : ℕ)
    (s : KoszulSlot (variableList k σ).length (j+1)) (a : coefficientModule k σ M) :
    koszulExteriorBoundary k σ M b j (a ⊗ₜ[k] koszulExteriorBasis (σ:=σ) k (j+1) s)=
      ∑ x : σ,((MvPolynomial.X x : VariableRing k σ) • a) ⊗ₜ[k]
        koszulExteriorContraction k σ j (LinearMap.proj x)
          (koszulExteriorBasis (σ:=σ) k (j+1) s) := by
  unfold koszulExteriorBoundary
  change koszulExteriorTensorEquiv k σ M b j
    (((coefficientKoszulListFunctor k σ (variableList k σ)).obj M).d (j+1) j
      ((koszulExteriorTensorEquiv k σ M b (j+1)).symm
        (a ⊗ₜ[k] koszulExteriorBasis (σ:=σ) k (j+1) s)))=_
  rw [← koszulExteriorTensorEquiv_slot k σ M b (j+1) s a,LinearEquiv.symm_apply_apply]
  exact koszulExteriorTensorEquiv_boundary_contraction_slot k σ M b j s a

theorem koszulExteriorBoundary_tmul (j : ℕ) (a : coefficientModule k σ M)
    (w : ⋀[k]^(j+1) (σ → k)) :
    koszulExteriorBoundary k σ M b j (a ⊗ₜ[k] w)=
      ∑ x : σ,((MvPolynomial.X x : VariableRing k σ) • a) ⊗ₜ[k]
        koszulExteriorContraction k σ j (LinearMap.proj x) w := by
  have h : (koszulExteriorBoundary k σ M b j).comp
      (TensorProduct.mk k (coefficientModule k σ M) (⋀[k]^(j+1) (σ → k)) a)=
    ∑ x : σ,(TensorProduct.mk k (coefficientModule k σ M) (⋀[k]^j (σ → k))
      ((MvPolynomial.X x : VariableRing k σ) • a)).comp (koszulExteriorContraction k σ j (LinearMap.proj x)) := by
    apply (koszulExteriorBasis (σ:=σ) k (j+1)).ext
    intro s
    change koszulExteriorBoundary k σ M b j (a ⊗ₜ[k] koszulExteriorBasis (σ:=σ) k (j+1) s)=_
    rw [koszulExteriorBoundary_tmul_basis]
    simp only [LinearMap.sum_apply,LinearMap.comp_apply,TensorProduct.mk_apply]
  simpa only [LinearMap.sum_apply,LinearMap.comp_apply,TensorProduct.mk_apply] using LinearMap.congr_fun h w
end NSP14.Homological
