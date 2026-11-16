module
public import NSP14.Width.EdgeHoleAction
public import NSP14.Homological.KoszulCombinedMinor
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open scoped Classical
open CategoryTheory NSP14.Homological
namespace NSP14.Endpoint.Data.OneHole
variable {D : NSP14.Endpoint.Data} (H : D.OneHole)

def block (p : Bool) : Finset D.a := Finset.univ.filter (fun b => H.side b=p)

abbrev MinorIndex (j : ℕ) := {p : Bool × KoszulWedge D.a j // ¬H.block p.1 ⊆ p.2.val}
noncomputable instance (j : ℕ) : Fintype (H.MinorIndex j) := by unfold MinorIndex; infer_instance

noncomputable def selected {j : ℕ} (a : H.MinorIndex j) : D.a :=
  (Finset.not_subset.mp a.property).choose

theorem selected_side {j : ℕ} (a : H.MinorIndex j) : H.side (H.selected a)=a.val.1 :=
  (Finset.mem_filter.mp (Finset.not_subset.mp a.property).choose_spec.1).2

theorem selected_not_mem {j : ℕ} (a : H.MinorIndex j) : H.selected a∉a.val.2.val :=
  (Finset.not_subset.mp a.property).choose_spec.2

variable (k : Type) [Field k]
noncomputable def target {j : ℕ} (a : H.MinorIndex j) : KoszulSlot (variableList k D.a).length j :=
  (koszulVariableWedgeEquiv k D.a j).symm a.val.2

theorem target_wedge {j : ℕ} (a : H.MinorIndex j) :
    koszulSlotWedge (variableList k D.a) j (H.target k a)=a.val.2.val :=
  congrArg Subtype.val ((koszulVariableWedgeEquiv k D.a j).apply_symm_apply a.val.2)

noncomputable def insertion {j : ℕ} (a : H.MinorIndex j) :
    KoszulSlot (variableList k D.a).length (j+1) × Bool :=
  let hex := koszulSlot_insert_partner (variableList k D.a) j (H.target k a)
    (H.selected a) (mem_variableList k D.a _) (by rw [H.target_wedge]; exact H.selected_not_mem a)
  (hex.choose,hex.choose_spec.choose)

theorem insertion_arrow {j : ℕ} (a : H.MinorIndex j) :
    koszulSlotArrow (variableList k D.a) j (H.insertion k a).1 (H.target k a)=
      some (H.selected a,(H.insertion k a).2) :=
  (koszulSlot_insert_partner (variableList k D.a) j (H.target k a)
    (H.selected a) (mem_variableList k D.a _) (by rw [H.target_wedge]; exact H.selected_not_mem a)).choose_spec.choose_spec.2

theorem insertion_wedge {j : ℕ} (a : H.MinorIndex j) :
    koszulSlotWedge (variableList k D.a) (j+1) (H.insertion k a).1=
      insert (H.selected a) a.val.2.val := by
  have he := (koszulSlotArrow_wedge (variableList k D.a) (variableList_nodup k D.a) j
    (H.insertion k a).1 (H.target k a) (H.selected a) (H.insertion k a).2 (H.insertion_arrow k a)).1
  rw [H.target_wedge] at he
  exact he.trans (by ext x; simp only [Finset.mem_insert])

noncomputable def column {j : ℕ} (a : H.MinorIndex j) : (coefficientKoszulComplex k D.a (D.QCoreModule k)).X (j+1) :=
  coefficientSlotIn k D.a (D.QCoreModule k) (variableList k D.a) (j+1) (H.insertion k a).1
    (D.coreColumn k (D.coreGeneratorPoint (D.internalVariable (H.mate (H.selected a)))))

noncomputable def row {j : ℕ} (a : H.MinorIndex j) :
    (coefficientKoszulComplex k D.a (D.QCoreModule k)).X j →ₗ[k] k :=
  (D.coreRow k (H.quadraticIndex (H.selected a))).comp
    (coefficientSlotOut k D.a (D.QCoreModule k) (variableList k D.a) j (H.target k a))

theorem entry {j : ℕ} (a b : H.MinorIndex j) :
    H.row k a (((coefficientKoszulComplex k D.a (D.QCoreModule k)).d (j+1) j).hom (H.column k b))=
      D.coreRow k (H.quadraticIndex (H.selected a))
        ((koszulSignedVariable k D.a (D.QCoreModule k)
          (koszulSlotArrow (variableList k D.a) j (H.insertion k b).1 (H.target k a))).hom
          (D.coreColumn k (D.coreGeneratorPoint (D.internalVariable (H.mate (H.selected b)))))) := by
  exact congrArg (D.coreRow k (H.quadraticIndex (H.selected a)))
    (coefficientSlot_d_arrow k D.a (D.QCoreModule k) (variableList k D.a) j
      (H.insertion k b).1 (H.target k a) _)

theorem diagonal {j : ℕ} (a : H.MinorIndex j) :
    H.row k a (((coefficientKoszulComplex k D.a (D.QCoreModule k)).d (j+1) j).hom (H.column k a))=1 ∨
    H.row k a (((coefficientKoszulComplex k D.a (D.QCoreModule k)).d (j+1) j).hom (H.column k a))= -1 := by
  rw [H.entry,H.insertion_arrow]
  cases hb : (H.insertion k a).2
  · left
    change D.coreRow k (H.quadraticIndex (H.selected a))
      ((MvPolynomial.X (H.selected a) : D.InternalRing k) •
        D.coreColumn k (D.coreGeneratorPoint (D.internalVariable (H.mate (H.selected a)))))=1
    rw [H.quadratic_variable_coefficient]
    simp
  · right
    change D.coreRow k (H.quadraticIndex (H.selected a))
      (-((MvPolynomial.X (H.selected a) : D.InternalRing k) •
        D.coreColumn k (D.coreGeneratorPoint (D.internalVariable (H.mate (H.selected a))))))= -1
    rw [map_neg,H.quadratic_variable_coefficient]
    simp

theorem arrow_off_diagonal {j : ℕ} (a b : H.MinorIndex j) (hab : a≠b)
    (v : D.a) (sign : Bool)
    (har : koszulSlotArrow (variableList k D.a) j (H.insertion k b).1 (H.target k a)=some (v,sign)) :
    ¬(H.side (H.selected b)=H.side (H.selected a) ∧ v=H.selected b) := by
  rintro ⟨hs,rfl⟩
  obtain ⟨hw,hn,_⟩ := koszulSlotArrow_wedge (variableList k D.a) (variableList_nodup k D.a) j
    (H.insertion k b).1 (H.target k a) (H.selected b) sign har
  rw [H.target_wedge] at hw hn
  have he := congrArg (fun F : Finset D.a => F.erase (H.selected b)) ((H.insertion_wedge k b).symm.trans hw)
  have he' : b.val.2.val=a.val.2.val := by
    ext x
    have hx := congrArg (fun F : Finset D.a => x∈F) he
    by_cases hxb : x=H.selected b
    · subst x
      simp only [H.selected_not_mem b,hn]
    · have hx' := Eq.to_iff hx
      simp only [Finset.mem_erase,Finset.mem_insert] at hx'
      tauto
  apply hab
  apply Subtype.ext
  apply Prod.ext
  · exact (H.selected_side a).symm.trans (hs.symm.trans (H.selected_side b))
  · exact Subtype.ext he'.symm

theorem off_diagonal {j : ℕ} (a b : H.MinorIndex j) (hab : a≠b) :
    H.row k a (((coefficientKoszulComplex k D.a (D.QCoreModule k)).d (j+1) j).hom (H.column k b))=0 := by
  rw [H.entry]
  cases har : koszulSlotArrow (variableList k D.a) j (H.insertion k b).1 (H.target k a) with
  | none => simp [koszulSignedVariable]
  | some p =>
    rcases p with ⟨v,sign⟩
    have hn := H.arrow_off_diagonal k a b hab v sign har
    cases sign
    · change D.coreRow k (H.quadraticIndex (H.selected a))
        ((MvPolynomial.X v : D.InternalRing k) •
          D.coreColumn k (D.coreGeneratorPoint (D.internalVariable (H.mate (H.selected b)))))=0
      rw [H.quadratic_variable_coefficient,ite_eq_right hn]
    · change D.coreRow k (H.quadraticIndex (H.selected a))
        (-((MvPolynomial.X v : D.InternalRing k) •
          D.coreColumn k (D.coreGeneratorPoint (D.internalVariable (H.mate (H.selected b))))))=0
      rw [map_neg,H.quadratic_variable_coefficient,ite_eq_right hn,neg_zero]

theorem upper_zero {j : ℕ} (s : KoszulSlot (variableList k D.a).length (j+1)) (a : H.MinorIndex j) :
    koszulImageRow k D.a (D.QCoreModule k) (D.QCoreLinearFunctional k) j s
      (((coefficientKoszulComplex k D.a (D.QCoreModule k)).d (j+1) j).hom (H.column k a))=0 := by
  have he := congrArg (D.QCoreLinearFunctional k (koszulSlotSelectedVariable k D.a j s))
    (coefficientSlot_d_arrow k D.a (D.QCoreModule k) (variableList k D.a) j
      (H.insertion k a).1 (koszulDeleteData k D.a j s).1
      (D.coreColumn k (D.coreGeneratorPoint (D.internalVariable (H.mate (H.selected a))))))
  change koszulImageRow k D.a (D.QCoreModule k) (D.QCoreLinearFunctional k) j s
    (((coefficientKoszulComplex k D.a (D.QCoreModule k)).d (j+1) j).hom (H.column k a))=_ at he
  rw [he]
  cases har : koszulSlotArrow (variableList k D.a) j (H.insertion k a).1 (koszulDeleteData k D.a j s).1 with
  | none => simp [koszulSignedVariable]
  | some p =>
    rcases p with ⟨v,sign⟩
    cases sign <;> simp [koszulSignedVariable,H.linear_variable_linear_zero]

theorem lower_zero {j : ℕ} (a : H.MinorIndex j) (s : KoszulSlot (variableList k D.a).length (j+1)) :
    H.row k a (((coefficientKoszulComplex k D.a (D.QCoreModule k)).d (j+1) j).hom
      (koszulUnitColumn k D.a (D.QCoreModule k) (D.QCoreUnit k) j s))=0 := by
  have he := congrArg (D.coreRow k (H.quadraticIndex (H.selected a)))
    (coefficientSlot_d_arrow k D.a (D.QCoreModule k) (variableList k D.a) j s (H.target k a) (D.QCoreUnit k))
  change H.row k a (((coefficientKoszulComplex k D.a (D.QCoreModule k)).d (j+1) j).hom
    (koszulUnitColumn k D.a (D.QCoreModule k) (D.QCoreUnit k) j s))=_ at he
  rw [he]
  cases har : koszulSlotArrow (variableList k D.a) j s (H.target k a) with
  | none => simp [koszulSignedVariable]
  | some p =>
    rcases p with ⟨v,sign⟩
    cases sign <;> simp [koszulSignedVariable,H.quadratic_variable_unit_zero]

theorem actual_boundary_rank (j : ℕ) :
    D.q.choose (j+1)+Fintype.card (H.MinorIndex j) ≤ koszulBoundaryRank k D.a (D.QCoreModule k) (j+1) := by
  have h := koszulBoundaryRank_ge_choose_add k D.a (D.QCoreModule k)
    (D.QCoreUnit k) (D.QCoreLinearFunctional k) (by
      intro v w
      by_cases he : v=w <;> simpa only [he,ite_true,ite_false] using D.QCore_linear_functionals k v w) j
    (H.column k) (H.row k) (H.diagonal k) (H.off_diagonal k) (H.upper_zero k) (H.lower_zero k)
  simpa only [Fintype.card_coe,q] using h
end NSP14.Endpoint.Data.OneHole
