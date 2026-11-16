module
public import NSP14.Homological.KoszulCoefficientSlots
public import NSP14.Homological.KoszulSlotDelete
public import NSP14.Homological.FunctionalMinor
public import NSP14.Homological.FiniteKoszulEuler
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory
open scoped Classical BigOperators
namespace NSP14.Homological
universe u
variable (k σ : Type u) [Field k] [Fintype σ]
  (M : ModuleCat.{u} (VariableRing k σ))
  (u₀ : coefficientModule k σ M)
  (ρ : σ → coefficientModule k σ M →ₗ[k] k)
  (hρ : ∀ v w,ρ v ((MvPolynomial.X w : VariableRing k σ) • u₀)=if v=w then 1 else 0)

noncomputable def koszulDeleteData (j : ℕ) (s : KoszulSlot (variableList k σ).length (j+1)) :
    KoszulSlot (variableList k σ).length j × Bool :=
  let h := koszulSlot_delete_partner k σ j s (koszulSlotSelectedVariable k σ j s)
    (koszulSlotSelectedVariable_mem k σ j s)
  (h.choose,h.choose_spec.choose)

theorem koszulDeleteData_wedge (j : ℕ) (s : KoszulSlot (variableList k σ).length (j+1)) :
    koszulSlotWedge (variableList k σ) j (koszulDeleteData k σ j s).1=
      (koszulSlotWedge (variableList k σ) (j+1) s).erase (koszulSlotSelectedVariable k σ j s) :=
  (koszulSlot_delete_partner k σ j s (koszulSlotSelectedVariable k σ j s)
    (koszulSlotSelectedVariable_mem k σ j s)).choose_spec.choose_spec.1

theorem koszulDeleteData_arrow (j : ℕ) (s : KoszulSlot (variableList k σ).length (j+1)) :
    koszulSlotArrow (variableList k σ) j s (koszulDeleteData k σ j s).1=
      some (koszulSlotSelectedVariable k σ j s,(koszulDeleteData k σ j s).2) :=
  (koszulSlot_delete_partner k σ j s (koszulSlotSelectedVariable k σ j s)
    (koszulSlotSelectedVariable_mem k σ j s)).choose_spec.choose_spec.2

noncomputable def koszulUnitColumn (j : ℕ) (s : KoszulSlot (variableList k σ).length (j+1)) :
    (coefficientKoszulComplex k σ M).X (j+1) :=
  coefficientSlotIn k σ M (variableList k σ) (j+1) s u₀

noncomputable def koszulImageRow (j : ℕ) (s : KoszulSlot (variableList k σ).length (j+1)) :
    (coefficientKoszulComplex k σ M).X j →ₗ[k] k :=
  (ρ (koszulSlotSelectedVariable k σ j s)).comp
    (coefficientSlotOut k σ M (variableList k σ) j (koszulDeleteData k σ j s).1)

theorem koszulImageEntry (j : ℕ) (s t : KoszulSlot (variableList k σ).length (j+1)) :
    koszulImageRow k σ M ρ j s (((coefficientKoszulComplex k σ M).d (j+1) j).hom (koszulUnitColumn k σ M u₀ j t))=
      ρ (koszulSlotSelectedVariable k σ j s)
        ((koszulSignedVariable k σ M (koszulSlotArrow (variableList k σ) j t (koszulDeleteData k σ j s).1)).hom u₀) := by
  exact congrArg (ρ (koszulSlotSelectedVariable k σ j s))
    (coefficientSlot_d_arrow k σ M (variableList k σ) j t (koszulDeleteData k σ j s).1 u₀)

include hρ in
theorem koszulImageEntry_diag (j : ℕ) (s : KoszulSlot (variableList k σ).length (j+1)) :
    koszulImageRow k σ M ρ j s (((coefficientKoszulComplex k σ M).d (j+1) j).hom (koszulUnitColumn k σ M u₀ j s))=1 ∨
    koszulImageRow k σ M ρ j s (((coefficientKoszulComplex k σ M).d (j+1) j).hom (koszulUnitColumn k σ M u₀ j s))= -1 := by
  rw [koszulImageEntry,koszulDeleteData_arrow]
  cases hb : (koszulDeleteData k σ j s).2 <;> simp [koszulSignedVariable,hρ]

include hρ in
theorem koszulImageEntry_offDiagonal (j : ℕ) (s t : KoszulSlot (variableList k σ).length (j+1)) (hst : s≠t) :
    koszulImageRow k σ M ρ j s (((coefficientKoszulComplex k σ M).d (j+1) j).hom (koszulUnitColumn k σ M u₀ j t))=0 := by
  rw [koszulImageEntry]
  cases ha : koszulSlotArrow (variableList k σ) j t (koszulDeleteData k σ j s).1 with
  | none => simp [koszulSignedVariable]
  | some p =>
    rcases p with ⟨v,b⟩
    have hne : koszulSlotSelectedVariable k σ j s≠v := by
      intro he
      subst v
      have hw := (koszulSlotArrow_wedge (variableList k σ) (variableList_nodup k σ) j
        t (koszulDeleteData k σ j s).1 (koszulSlotSelectedVariable k σ j s) b ha).1
      rw [koszulDeleteData_wedge,Finset.insert_erase (koszulSlotSelectedVariable_mem k σ j s)] at hw
      exact hst (koszulSlotWedge_injective _ (variableList_nodup k σ) (j+1) hw).symm
    cases b <;> simp [koszulSignedVariable,hρ,hne]

include hρ in
theorem koszulBoundaryRank_ge_choose [Module.Finite k (coefficientModule k σ M)] (j : ℕ) :
    (Fintype.card σ).choose (j+1) ≤ koszulBoundaryRank k σ M (j+1) := by
  let : Module.Finite k ((coefficientKoszulComplex k σ M).X j) :=
    koszul_chain_coefficient_finite k σ (variableList k σ) M j
  let A : Matrix (KoszulSlot (variableList k σ).length (j+1))
      (KoszulSlot (variableList k σ).length (j+1)) k :=
    fun s t => koszulImageRow k σ M ρ j s
      (((coefficientKoszulComplex k σ M).d (j+1) j).hom (koszulUnitColumn k σ M u₀ j t))
  have he : A=Matrix.diagonal (fun s => A s s) := by
    ext s t
    by_cases h : s=t
    · subst t;simp
    · rw [Matrix.diagonal_apply,ite_eq_right h]
      exact koszulImageEntry_offDiagonal k σ M u₀ ρ hρ j s t h
  have hd : Matrix.det A ≠ 0 := by
    rw [he,Matrix.det_diagonal]
    apply Finset.prod_ne_zero_iff.mpr
    intro s _
    rcases koszulImageEntry_diag k σ M u₀ ρ hρ j s with h|h <;> simp [A] at h ⊢ <;> simp [h]
  have h := functional_minor_rank_lower_bound k ((coefficientKoszulComplex k σ M).d (j+1) j).hom
    (koszulUnitColumn k σ M u₀ j) (koszulImageRow k σ M ρ j) hd
  rw [koszulSlot_card,variableList_length] at h
  simpa only [koszulBoundaryRank,chainBoundaryRank_succ] using h
end NSP14.Homological
