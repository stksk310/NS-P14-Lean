module
public import NSP14.ArithmeticSequence.HeadQuotientMap
public import NSP14.Semigroup.HeadDegree
@[expose] public section
open scoped Classical
namespace NSP14.ArithmeticSequence.Data
variable (D : NSP14.ArithmeticSequence.Data)

theorem blockCount_monotone : Monotone D.blockCount := by
  intro i j hij
  exact (D.blockCount_le_iff i _).mpr (hij.trans (D.index_le_blocks j))

theorem aperyValue_strictMono : StrictMono D.aperyValue := by
  intro i j hij
  have h := D.blockCount_monotone (Nat.le_of_lt hij)
  have hd := D.d_pos
  unfold aperyValue
  nlinarith

noncomputable def headIndexEquiv : Fin D.m ≃ D.source.HeadExponent :=
  Equiv.ofBijective
    (fun i => ⟨⟨D.aperyValue i.val,D.aperyValue_mem_source i.val⟩,
      (D.head_iff_apery _).mpr (D.aperyValue_mem i.isLt)⟩)
    ⟨by
      intro i j he
      apply Fin.ext
      exact D.aperyValue_strictMono.injective (congrArg (fun a : D.source.HeadExponent => a.val.val) he),
     by
      intro a
      obtain ⟨i,hi,he⟩ := (D.mem_apery_iff a.val.val).mp ((D.head_iff_apery _).mp a.property)
      exact ⟨⟨i,hi⟩,Subtype.ext (Subtype.ext he.symm)⟩⟩

theorem headIndexEquiv_value (i : Fin D.m) : (D.headIndexEquiv i).val.val=D.aperyValue i.val := rfl

theorem aperyValue_not_apery {i : ℕ} (hi : D.m ≤ i) : D.aperyValue i ∉ D.source.aperySet := by
  intro ha
  have hd := D.d_pos
  have hn : D.blockCount i ≤ D.blockCount i+D.d-1 := by omega
  have hc : i-D.m ≤ D.v*(D.blockCount i+D.d-1) :=
    (Nat.sub_le _ _).trans ((D.index_le_blocks i).trans (Nat.mul_le_mul_left D.v hn))
  have hp : (D.blockCount i+D.d-1)*D.m+(i-D.m)*D.d ∈ D.source :=
    ⟨D.blockCount i+D.d-1,i-D.m,hc,rfl⟩
  apply D.source.apery_no_predecessor ha
  rw [D.multiplicity]
  refine ⟨_,hp,?_⟩
  unfold aperyValue
  nlinarith [Nat.sub_add_cancel hi,
    Nat.sub_add_cancel (show 1 ≤ D.blockCount i+D.d by omega)]

variable (k : Type*) [CommRing k] [Nontrivial k]
noncomputable def headIndexMonomial (i : ℕ) : D.source.HeadAlgebra k :=
  D.source.headMonomial k ⟨D.aperyValue i,D.aperyValue_mem_source i⟩

theorem headIndexMonomial_zero {i : ℕ} (hi : D.m ≤ i) : D.headIndexMonomial k i=0 := by
  apply D.source.headMonomial_zero_of_not_head
  intro hh
  exact D.aperyValue_not_apery hi ((D.head_iff_apery _).mp hh)

theorem headIndexMonomial_basis (i : Fin D.m) :
    D.headIndexMonomial k i.val=D.source.headBasis k (D.headIndexEquiv i) :=
  D.source.headMonomial_eq_basis k (D.headIndexEquiv i)

variable (K : Type) [Field K]
omit [CommRing k] [Nontrivial k] in
/-- A literal multiplication table, including all out-of-range indices.
No initial-monomial Betti equality is inferred from this table. -/
theorem headIndexMonomial_mul (i j : ℕ) :
    D.headIndexMonomial K i*D.headIndexMonomial K j=
      if D.blockCount (i+j)=D.blockCount i+D.blockCount j
      then D.headIndexMonomial K (i+j) else 0 := by
  have hle : D.blockCount (i+j) ≤ D.blockCount i+D.blockCount j := by
    apply (D.blockCount_le_iff _ _).mpr
    nlinarith [D.index_le_blocks i,D.index_le_blocks j]
  change D.source.headMonomial K _*D.source.headMonomial K _=_
  rw [D.headMonomial_mul]
  by_cases he : D.blockCount (i+j)=D.blockCount i+D.blockCount j
  · rw [ite_eq_left he]
    apply congrArg (D.source.headMonomial K)
    apply Subtype.ext
    change D.aperyValue i+D.aperyValue j=D.aperyValue (i+j)
    unfold aperyValue
    rw [he]
    ring
  · rw [ite_eq_right he]
    apply D.source.headMonomial_zero_of_not_head
    intro hh
    have ha := (D.head_iff_apery _).mp hh
    have hb : D.blockCount (i+j) ≤ D.blockCount i+D.blockCount j-1 := by omega
    have hs : i+j ≤ D.v*(D.blockCount i+D.blockCount j-1) :=
      (D.index_le_blocks (i+j)).trans (Nat.mul_le_mul_left D.v hb)
    have hp : (D.blockCount i+D.blockCount j-1)*D.m+(i+j)*D.d ∈ D.source :=
      ⟨D.blockCount i+D.blockCount j-1,i+j,hs,rfl⟩
    apply D.source.apery_no_predecessor ha
    rw [D.multiplicity]
    refine ⟨_,hp,?_⟩
    change D.aperyValue i+D.aperyValue j=_
    unfold aperyValue
    nlinarith [Nat.sub_add_cancel (show 1 ≤ D.blockCount i+D.blockCount j by omega)]
end NSP14.ArithmeticSequence.Data
