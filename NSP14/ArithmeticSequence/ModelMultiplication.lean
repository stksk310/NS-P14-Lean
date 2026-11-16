module
public import NSP14.ArithmeticSequence.ModelCoordinates
@[expose] public section
open scoped Classical
namespace NSP14.ArithmeticSequence.Data
variable (D : NSP14.ArithmeticSequence.Data) (hv : 2 ≤ D.v)

theorem modelExponent_add {i j : ℕ}
    (h : D.blockCount (i+j)=D.blockCount i+D.blockCount j) :
    D.modelExponent i+D.modelExponent j=D.modelExponent (i+j) := by
  have hi := D.modelExponent_add_index i
  have hj := D.modelExponent_add_index j
  have hs := D.modelExponent_add_index (i+j)
  rw [h] at hs
  nlinarith only [hi,hj,hs]

theorem modelExponent_dead {i j : ℕ}
    (h : D.blockCount (i+j)≠D.blockCount i+D.blockCount j) :
    (D.ordinaryModel hv).source.order (D.modelExponent i+D.modelExponent j)>
      D.blockCount i+D.blockCount j := by
  have hle : D.blockCount (i+j) ≤ D.blockCount i+D.blockCount j := by
    apply (D.blockCount_le_iff _ _).mpr
    nlinarith [D.index_le_blocks i,D.index_le_blocks j]
  have hb : D.blockCount (i+j) ≤ D.blockCount i+D.blockCount j-1 := by omega
  have hs : i+j ≤ D.v*(D.blockCount i+D.blockCount j-1) :=
    (D.index_le_blocks (i+j)).trans (Nat.mul_le_mul_left D.v hb)
  have hi := D.modelExponent_add_index i
  have hj := D.modelExponent_add_index j
  have hn : D.blockCount i+D.blockCount j-1+1=D.blockCount i+D.blockCount j :=
    Nat.sub_add_cancel (by omega)
  have ha : (D.blockCount i+D.blockCount j+1)*D.v ≤ D.modelExponent i+D.modelExponent j := by
    nlinarith only [hs,hi,hj,hn]
  rw [D.ordinaryModel_order hv ((D.ordinaryModel hv).source.add_mem
    (D.modelExponent_mem hv i) (D.modelExponent_mem hv j))]
  exact Nat.lt_of_succ_le ((Nat.le_div_iff_mul_le (by have := D.v_pos;omega)).mpr ha)

variable (k : Type) [Field k]
noncomputable def modelMonomial (i : ℕ) : (D.ordinaryModel hv).source.TangentAlgebra k :=
  (D.ordinaryModel hv).source.initialMonomial k ⟨D.modelExponent i,D.modelExponent_mem hv i⟩

theorem modelMonomial_mul (i j : ℕ) :
    D.modelMonomial hv k i*D.modelMonomial hv k j=
      if D.blockCount (i+j)=D.blockCount i+D.blockCount j
      then D.modelMonomial hv k (i+j) else 0 := by
  by_cases he : D.blockCount (i+j)=D.blockCount i+D.blockCount j
  · rw [ite_eq_left he]
    have ha : (⟨D.modelExponent i,D.modelExponent_mem hv i⟩ : (D.ordinaryModel hv).source.carrier)+
        ⟨D.modelExponent j,D.modelExponent_mem hv j⟩=
        ⟨D.modelExponent (i+j),D.modelExponent_mem hv (i+j)⟩ :=
      Subtype.ext (D.modelExponent_add he)
    have hl : (D.ordinaryModel hv).source.order (D.modelExponent i+D.modelExponent j)=
        (D.ordinaryModel hv).source.order (D.modelExponent i)+
          (D.ordinaryModel hv).source.order (D.modelExponent j) := by
      rw [D.modelExponent_add he,D.modelExponent_order hv,D.modelExponent_order hv,D.modelExponent_order hv,he]
    change (D.ordinaryModel hv).source.initialMonomial k _*(D.ordinaryModel hv).source.initialMonomial k _=_
    rw [(D.ordinaryModel hv).source.initialMonomial_mul_live k _ _ hl,ha]
    rfl
  · rw [ite_eq_right he]
    apply ((D.ordinaryModel hv).source.initialMonomial_mul_eq_zero_iff k _ _).mpr
    rw [D.modelExponent_order hv,D.modelExponent_order hv]
    exact D.modelExponent_dead hv he
end NSP14.ArithmeticSequence.Data
