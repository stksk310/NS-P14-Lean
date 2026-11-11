module
public import NSP14.Homological.ActionH0Ideal
public import NSP14.Homological.ConeExactness
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits HomologicalComplex
namespace NSP14.Endpoint
variable (R : Type) [CommRing R]

theorem action_piece_isZero_of_gt (xs : List R) (M : ModuleCat R) (i : ℕ)
    (hi : xs.length < i) : IsZero ((NSP14.Homological.actionKoszul R xs M).X i) := by
  induction xs generalizing i with
  | nil => exact HomologicalComplex.isZero_single_obj_X (ComplexShape.down ℕ) 0 M i (by simpa using Nat.ne_zero_of_lt hi)
  | cons x xs ih =>
    apply homotopyCofiber.isZero_X (x • 𝟙 (NSP14.Homological.actionKoszul R xs M)) i
    · exact ih i (by simp only [List.length_cons] at hi;omega)
    · intro j hj
      have he : j+1=i := hj
      exact ih j (by simp only [List.length_cons] at hi;omega)

open NSP14.Homological
variable (r : R) (M : ModuleCat R)

noncomputable def singleActionOneEquiv : (actionKoszul R [r] M).X 1 ≃ₗ[R] M where
  toFun := coneFirst (actionKoszul R [] M) r 0
  invFun := (homotopyCofiber.inlX (r • 𝟙 (actionKoszul R [] M)) 0 1 rfl).hom
  map_add' := (coneFirst (actionKoszul R [] M) r 0).map_add
  map_smul' := (coneFirst (actionKoszul R [] M) r 0).map_smul
  left_inv z := by
    apply cone_element_ext (actionKoszul R [] M) r 0
    · exact coneFirst_inl _ _ _ _
    · have : Subsingleton ((actionKoszul R [] M).X 1) :=
        ModuleCat.subsingleton_of_isZero (action_piece_isZero_of_gt R [] M 1 (by simp))
      exact Subsingleton.elim _ _
  right_inv a := coneFirst_inl _ _ _ _

theorem singleAction_differential (z : (actionKoszul R [r] M).X 1) :
    actionZeroDifferential R [r] M z=r • singleActionOneEquiv R r M z := by
  have h := actionZeroDifferential_cons_left R r [] M (singleActionOneEquiv R r M z)
  change actionZeroDifferential R [r] M ((singleActionOneEquiv R r M).symm
    (singleActionOneEquiv R r M z))=r • singleActionOneEquiv R r M z at h
  rw [LinearEquiv.symm_apply_apply] at h
  exact h

noncomputable def singleActionCycleEquiv :
    ((actionKoszul R [r] M).d 1 0).hom.ker ≃ₗ[R] (r • (𝟙 M)).hom.ker where
  toFun z := ⟨singleActionOneEquiv R r M z.val,by
    change r • singleActionOneEquiv R r M z.val=0
    rw [←singleAction_differential]
    change (actionZeroIso R [r] M).hom ((actionKoszul R [r] M).d 1 0 z.val)=0
    rw [show (actionKoszul R [r] M).d 1 0 z.val=0 from z.property,map_zero]⟩
  invFun z := ⟨(singleActionOneEquiv R r M).symm z.val,by
    apply (actionZeroIso R [r] M).toLinearEquiv.injective
    change actionZeroDifferential R [r] M ((singleActionOneEquiv R r M).symm z.val)=
      (actionZeroIso R [r] M).hom 0
    rw [singleAction_differential,LinearEquiv.apply_symm_apply,map_zero]
    exact z.property⟩
  left_inv z := Subtype.ext ((singleActionOneEquiv R r M).symm_apply_apply z.val)
  right_inv z := Subtype.ext ((singleActionOneEquiv R r M).apply_symm_apply z.val)
  map_add' a b := Subtype.ext ((singleActionOneEquiv R r M).map_add a.val b.val)
  map_smul' c a := Subtype.ext ((singleActionOneEquiv R r M).map_smul c a.val)

/-- H1 of a genuine one-element Koszul complex is its genuine kernel;
no finite-chain hypothesis occurs. -/
noncomputable def singleActionH1Equiv : (actionKoszul R [r] M).homology 1 ≃ₗ[R] (r • (𝟙 M)).hom.ker := by
  let K := actionKoszul R [r] M
  have hf : (K.sc' 2 1 0).f=0 :=
    (action_piece_isZero_of_gt R [r] M 2 (by simp)).eq_of_src _ _
  exact ((K.homologyIsoSc' 2 1 0 ((ComplexShape.down ℕ).prev_eq' rfl) ((ComplexShape.down ℕ).next_eq' rfl)) ≪≫
    ((K.sc' 2 1 0).asIsoHomologyπ hf).symm ≪≫
    (K.sc' 2 1 0).moduleCatCyclesIso).toLinearEquiv.trans (singleActionCycleEquiv R r M)
end NSP14.Endpoint
