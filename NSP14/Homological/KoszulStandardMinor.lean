module
public import NSP14.Homological.WedgeExponent
public import NSP14.Homological.FunctionalMinor
public import NSP14.Homological.FiniteKoszulEuler
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory
open scoped Classical BigOperators
namespace NSP14.Homological
universe u
variable (k σ : Type u) [Field k] [Fintype σ]
  (M : ModuleCat.{u} (VariableRing k σ)) (m : MonomialOrder σ)
  {q : ℕ} (g : Fin q → coefficientModule k σ M)

abbrev StandardKoszulTarget (j : ℕ) :=
  ModuleStandard k m g × KoszulSlot (variableList k σ).length j

noncomputable def standardKoszulTerm {j : ℕ} (a : StandardKoszulTarget k σ M m g j) :
    ModuleTerm m (q:=q) :=
  moduleTermShift m (wedgeExponent (koszulSlotWedge (variableList k σ) j a.2)) a.1.val

/-- A pivot is chosen for each augmented term, hence is shared by all
exterior rows in that term. The choice will later maximize a finite count. -/
noncomputable def PivotKoszulTarget (j : ℕ) (p : ModuleTerm m (q:=q) → σ) :=
  {a : StandardKoszulTarget k σ M m g j //
    p (standardKoszulTerm k σ M m g a) ∉ koszulSlotWedge (variableList k σ) j a.2 ∧
    0 < moduleTermExponent m a.1.val (p (standardKoszulTerm k σ M m g a))}

variable {j : ℕ} (p : ModuleTerm m (q:=q) → σ)
local notation "PT" => PivotKoszulTarget k σ M m g j p

noncomputable def pivotKoszulDivisor (a : PT) : ModuleStandard k m g :=
  moduleStandardDivide m k g (p (standardKoszulTerm k σ M m g a.val)) a.val.1 a.property.2

noncomputable def pivotKoszulPartner (a : PT) : KoszulSlot (variableList k σ).length (j+1) × Bool :=
  let h := koszulSlot_insert_partner (variableList k σ) j a.val.2
    (p (standardKoszulTerm k σ M m g a.val)) (mem_variableList k σ _) a.property.1
  (h.choose,h.choose_spec.choose)

theorem pivotKoszulPartner_wedge (a : PT) :
    koszulSlotWedge (variableList k σ) (j+1) (pivotKoszulPartner k σ M m g p a).1 =
      insert (p (standardKoszulTerm k σ M m g a.val))
        (koszulSlotWedge (variableList k σ) j a.val.2) :=
  (koszulSlot_insert_partner (variableList k σ) j a.val.2 _ (mem_variableList k σ _) a.property.1).choose_spec.choose_spec.1

theorem pivotKoszulPartner_arrow (a : PT) :
    koszulSlotArrow (variableList k σ) j (pivotKoszulPartner k σ M m g p a).1 a.val.2 =
      some (p (standardKoszulTerm k σ M m g a.val),(pivotKoszulPartner k σ M m g p a).2) :=
  (koszulSlot_insert_partner (variableList k σ) j a.val.2 _ (mem_variableList k σ _) a.property.1).choose_spec.choose_spec.2

variable (hg : Submodule.span (VariableRing k σ) (Set.range g)=⊤)

noncomputable def pivotKoszulColumn (a : PT) : (coefficientKoszulComplex k σ M).X (j+1) :=
  (koszulSlotIn k σ M (variableList k σ) (j+1) (pivotKoszulPartner k σ M m g p a).1).hom
    (moduleStandardBasis k m g hg (pivotKoszulDivisor k σ M m g p a))

noncomputable def pivotKoszulRow (a : PT) : (coefficientKoszulComplex k σ M).X j →ₗ[k] k :=
  ((moduleStandardBasis k m g hg).coord a.val.1).comp
    (((ModuleCat.restrictScalars (algebraMap k (VariableRing k σ))).map
      (koszulSlotOut k σ M (variableList k σ) j a.val.2)).hom)

theorem pivotKoszulEntry (a b : PT) :
    pivotKoszulRow k σ M m g p hg a
      (((coefficientKoszulComplex k σ M).d (j+1) j).hom (pivotKoszulColumn k σ M m g p hg b)) =
    (moduleStandardBasis k m g hg).repr
      ((koszulSignedVariable k σ M
        (koszulSlotArrow (variableList k σ) j (pivotKoszulPartner k σ M m g p b).1 a.val.2)).hom
          (moduleStandardBasis k m g hg (pivotKoszulDivisor k σ M m g p b))) a.val.1 := by
  change (moduleStandardBasis k m g hg).repr
    ((koszulSlotIn k σ M (variableList k σ) (j+1) (pivotKoszulPartner k σ M m g p b).1 ≫
      (koszulList k σ (variableList k σ) M).d (j+1) j ≫
        koszulSlotOut k σ M (variableList k σ) j a.val.2).hom
          (moduleStandardBasis k m g hg (pivotKoszulDivisor k σ M m g p b))) a.val.1 = _
  rw [koszulSlot_d_arrow]

theorem pivotKoszul_divisor_shift (a : PT) :
    moduleTermShift m (Finsupp.single (p (standardKoszulTerm k σ M m g a.val)) 1)
      (pivotKoszulDivisor k σ M m g p a).val=a.val.1.val :=
  moduleTermShift_divide m _ _ a.property.2

theorem pivotKoszul_divisor_action (a : PT) :
    (MvPolynomial.X (p (standardKoszulTerm k σ M m g a.val)) : VariableRing k σ) •
      moduleStandardBasis k m g hg (pivotKoszulDivisor k σ M m g p a)=
        moduleStandardBasis k m g hg a.val.1 := by
  rw [moduleStandardBasis_apply,moduleStandardBasis_apply]
  change (MvPolynomial.monomial (Finsupp.single _ 1) (1:k)) • _ = _
  rw [← moduleTermVector_shift,pivotKoszul_divisor_shift]

theorem pivotKoszulEntry_diag (a : PT) :
    pivotKoszulRow k σ M m g p hg a
      (((coefficientKoszulComplex k σ M).d (j+1) j).hom (pivotKoszulColumn k σ M m g p hg a))=1 ∨
    pivotKoszulRow k σ M m g p hg a
      (((coefficientKoszulComplex k σ M).d (j+1) j).hom (pivotKoszulColumn k σ M m g p hg a))= -1 := by
  rw [pivotKoszulEntry,pivotKoszulPartner_arrow]
  cases h : (pivotKoszulPartner k σ M m g p a).2 <;>
    simp [koszulSignedVariable,pivotKoszul_divisor_action k σ M m g p hg a]

theorem pivotKoszulArrow_term (a b : PT) (v : σ) (s : Bool)
    (ha : koszulSlotArrow (variableList k σ) j (pivotKoszulPartner k σ M m g p b).1 a.val.2=some (v,s)) :
    moduleTermShift m (wedgeExponent (koszulSlotWedge (variableList k σ) j a.val.2))
      (moduleTermShift m (Finsupp.single v 1) (pivotKoszulDivisor k σ M m g p b).val)=
        standardKoszulTerm k σ M m g b.val := by
  rw [moduleTermShift_add,koszulSlotArrow_exponent _ (variableList_nodup k σ) _ _ _ ha,
    pivotKoszulPartner_wedge,wedgeExponent_insert _ _ b.property.1,add_comm,
    ← moduleTermShift_add,pivotKoszul_divisor_shift]
  rfl

theorem pivotKoszulEntry_zero_of_lt (a b : PT)
    (hlt : standardKoszulTerm k σ M m g b.val < standardKoszulTerm k σ M m g a.val) :
    pivotKoszulRow k σ M m g p hg a
      (((coefficientKoszulComplex k σ M).d (j+1) j).hom (pivotKoszulColumn k σ M m g p hg b))=0 := by
  rw [pivotKoszulEntry]
  cases he : koszulSlotArrow (variableList k σ) j (pivotKoszulPartner k σ M m g p b).1 a.val.2 with
  | none => simp [koszulSignedVariable]
  | some z =>
    rcases z with ⟨v,s⟩
    have hkey := pivotKoszulArrow_term k σ M m g p a b v s he
    have hlt' : moduleTermShift m (Finsupp.single v 1) (pivotKoszulDivisor k σ M m g p b).val < a.val.1.val := by
      apply (moduleTermShift_strictMono m (wedgeExponent (koszulSlotWedge (variableList k σ) j a.val.2))).lt_iff_lt.mp
      rw [hkey]
      exact hlt
    have hc := moduleStandardBasis_shift_coeff_zero k m g hg (Finsupp.single v 1)
      (pivotKoszulDivisor k σ M m g p b) a.val.1 hlt'
    cases s <;> simpa [koszulSignedVariable,MvPolynomial.X] using hc

theorem pivotKoszulArrow_same_term (a b : PT)
    (ht : standardKoszulTerm k σ M m g a.val=standardKoszulTerm k σ M m g b.val)
    (v : σ) (s : Bool)
    (ha : koszulSlotArrow (variableList k σ) j (pivotKoszulPartner k σ M m g p b).1 a.val.2=some (v,s)) : a=b := by
  have hn : p (standardKoszulTerm k σ M m g b.val) ∉ koszulSlotWedge (variableList k σ) j a.val.2 := by
    rw [← ht]
    exact a.property.1
  obtain ⟨hw,hv,_⟩ := koszulSlotArrow_wedge _ (variableList_nodup k σ) _ _ _ v s ha
  have hp : p (standardKoszulTerm k σ M m g b.val) ∈
      koszulSlotWedge (variableList k σ) (j+1) (pivotKoszulPartner k σ M m g p b).1 := by
    rw [pivotKoszulPartner_wedge]
    exact Finset.mem_insert_self _ _
  rw [hw] at hp
  have he : p (standardKoszulTerm k σ M m g b.val)=v := (Finset.mem_insert.mp hp).resolve_right hn
  rw [pivotKoszulPartner_wedge,← he] at hw
  have hF := congrArg (Finset.erase · (p (standardKoszulTerm k σ M m g b.val))) hw
  rw [Finset.erase_insert b.property.1,Finset.erase_insert hn] at hF
  have hs : a.val.2=b.val.2 := koszulSlotWedge_injective _ (variableList_nodup k σ) j hF.symm
  apply Subtype.ext
  apply Prod.ext
  · apply Subtype.ext
    apply (moduleTermShift_strictMono m (wedgeExponent (koszulSlotWedge (variableList k σ) j a.val.2))).injective
    simpa only [standardKoszulTerm,hs] using ht
  · exact hs

theorem pivotKoszulEntry_zero_of_same (a b : PT)
    (ht : standardKoszulTerm k σ M m g a.val=standardKoszulTerm k σ M m g b.val) (hne : a ≠ b) :
    pivotKoszulRow k σ M m g p hg a
      (((coefficientKoszulComplex k σ M).d (j+1) j).hom (pivotKoszulColumn k σ M m g p hg b))=0 := by
  have he : koszulSlotArrow (variableList k σ) j (pivotKoszulPartner k σ M m g p b).1 a.val.2=none := by
    cases h : koszulSlotArrow (variableList k σ) j (pivotKoszulPartner k σ M m g p b).1 a.val.2 with
    | none => rfl
    | some z => exact (hne (pivotKoszulArrow_same_term k σ M m g p a b ht z.1 z.2 h)).elim
  rw [pivotKoszulEntry,he]
  simp [koszulSignedVariable]

include hg in
/-- A genuine minor of the actual Koszul differential, with no initial-rank
comparison left as a hypothesis. Finiteness is required of M over k here. -/
theorem pivotKoszulTarget_rank [Module.Finite k (coefficientModule k σ M)] :
    Nat.card (PivotKoszulTarget k σ M m g j p) ≤ koszulBoundaryRank k σ M (j+1) := by
  let := moduleStandard_finite k m g hg
  let : Fintype (ModuleStandard k m g) := Fintype.ofFinite _
  let : Fintype PT := by unfold PivotKoszulTarget; infer_instance
  let key : PT → ModuleTerm m (q:=q) ×ₗ Fin (Fintype.card PT) :=
    fun a => toLex (standardKoszulTerm k σ M m g a.val,Fintype.equivFin PT a)
  have hk : Function.Injective key := by
    intro a b he
    exact (Fintype.equivFin PT).injective (congrArg (fun z => (ofLex z).2) he)
  let : LinearOrder PT := LinearOrder.lift' key hk
  let : Module.Finite k ((coefficientKoszulComplex k σ M).X j) :=
    koszul_chain_coefficient_finite k σ (variableList k σ) M j
  rw [Nat.card_eq_fintype_card]
  unfold koszulBoundaryRank
  rw [chainBoundaryRank_succ]
  apply triangular_functional_minor_rank_lower_bound k _
    (pivotKoszulColumn k σ M m g p hg) (pivotKoszulRow k σ M m g p hg)
  · intro a b hba
    have hne : a ≠ b := ne_of_gt hba
    change key b < key a at hba
    rw [Prod.Lex.lt_iff] at hba
    rcases hba with hlt | ⟨he,_⟩
    · exact pivotKoszulEntry_zero_of_lt k σ M m g p hg a b hlt
    · exact pivotKoszulEntry_zero_of_same k σ M m g p hg a b he.symm hne
  · exact pivotKoszulEntry_diag k σ M m g p hg
end NSP14.Homological
