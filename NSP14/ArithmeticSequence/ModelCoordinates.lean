module
public import NSP14.ArithmeticSequence.OrdinaryModel
public import NSP14.ArithmeticSequence.HeadIndex
@[expose] public section
namespace NSP14.ArithmeticSequence.Data
variable (D : NSP14.ArithmeticSequence.Data)

/-- Reflection inside a block identifies the ordinary-cone basis with
all nonnegative AP indices. This precedes the finite AP truncation. -/
def modelExponent (i : ℕ) : ℕ := 2*D.blockCount i*D.v-i

theorem blockCount_zero : D.blockCount 0=0 := by simp [blockCount]

theorem blockCount_pos {i : ℕ} (hi : 0 < i) : 0 < D.blockCount i := by
  have h := D.index_le_blocks i
  by_contra hn
  have he : D.blockCount i=0 := by omega
  rw [he,Nat.mul_zero] at h
  omega

theorem blockCount_pred_bound {i : ℕ} (hi : 0 < i) :
    D.v*(D.blockCount i-1) < i := by
  have hb := D.blockCount_pos hi
  by_contra hn
  have h := (D.blockCount_le_iff i (D.blockCount i-1)).mpr (by omega)
  omega

theorem modelExponent_add_index (i : ℕ) : D.modelExponent i+i=2*D.blockCount i*D.v := by
  apply Nat.sub_add_cancel
  nlinarith [D.index_le_blocks i]

theorem modelExponent_div (i : ℕ) : D.modelExponent i/D.v=D.blockCount i := by
  by_cases hz : i=0
  · subst i;simp [modelExponent,D.blockCount_zero]
  have hi : 0 < i := by omega
  have hl := D.index_le_blocks i
  have hb := D.blockCount_pred_bound hi
  have he := D.modelExponent_add_index i
  have hc := Nat.sub_add_cancel (show 1 ≤ D.blockCount i from D.blockCount_pos hi)
  apply Nat.div_eq_of_lt_le <;> nlinarith

theorem modelExponent_mem (hv : 2 ≤ D.v) (i : ℕ) :
    D.modelExponent i ∈ (D.ordinaryModel hv).source := by
  apply (D.ordinaryModel_mem hv _).mpr
  by_cases hz : i=0
  · left;subst i;simp [modelExponent,D.blockCount_zero]
  · right
    have hl := D.index_le_blocks i
    have hp := D.blockCount_pos (show 0 < i by omega)
    have he := D.modelExponent_add_index i
    nlinarith

theorem modelExponent_injective : Function.Injective D.modelExponent := by
  intro i j he
  have hd := congrArg (fun n => n/D.v) he
  rw [D.modelExponent_div,D.modelExponent_div] at hd
  have hi := D.modelExponent_add_index i
  have hj := D.modelExponent_add_index j
  rw [hd] at hi
  omega

theorem modelExponent_surjective (hv : 2 ≤ D.v) :
    ∀ x ∈ (D.ordinaryModel hv).source,∃ i,D.modelExponent i=x := by
  intro x hx
  rcases (D.ordinaryModel_mem hv x).mp hx with rfl|hx'
  · exact ⟨0,by simp [modelExponent,D.blockCount_zero]⟩
  let q := x/D.v
  let i := 2*q*D.v-x
  have hq : 1 ≤ q := Nat.div_pos hx' (by omega)
  have hr : x%D.v < D.v := Nat.mod_lt _ (by omega)
  have he : x%D.v+D.v*q=x := Nat.mod_add_div _ _
  have hxle : x ≤ 2*q*D.v := by nlinarith
  have hi : i+x=2*q*D.v := Nat.sub_add_cancel hxle
  have hib : i ≤ D.v*q := by nlinarith only [he,hi,Nat.zero_le (x%D.v)]
  have hp : D.v*(q-1) < i := by nlinarith [Nat.sub_add_cancel hq]
  have hb : D.blockCount i=q := by
    apply Nat.le_antisymm ((D.blockCount_le_iff i q).mpr hib)
    have hl := D.index_le_blocks i
    by_contra hn
    have hlt : D.blockCount i ≤ q-1 := by omega
    have hm := Nat.mul_le_mul_left D.v hlt
    omega
  refine ⟨i,?_⟩
  have hs := D.modelExponent_add_index i
  rw [hb] at hs
  omega

noncomputable def modelExponentEquiv (hv : 2 ≤ D.v) : ℕ ≃ (D.ordinaryModel hv).source.carrier :=
  Equiv.ofBijective (fun i => ⟨D.modelExponent i,D.modelExponent_mem hv i⟩)
    ⟨fun i j he => D.modelExponent_injective (congrArg Subtype.val he),by
      intro x
      obtain ⟨i,hi⟩ := D.modelExponent_surjective hv x.val x.property
      exact ⟨i,Subtype.ext hi⟩⟩

theorem modelExponent_order (hv : 2 ≤ D.v) (i : ℕ) :
    (D.ordinaryModel hv).source.order (D.modelExponent i)=D.blockCount i := by
  rw [D.ordinaryModel_order hv (D.modelExponent_mem hv i),D.modelExponent_div]

theorem blockCount_v : D.blockCount D.v=1 := by
  have hl := (D.blockCount_le_iff D.v 1).mpr (by simp)
  have hp := D.blockCount_pos D.v_pos
  omega

theorem blockCount_add_v (i : ℕ) : D.blockCount (i+D.v)=D.blockCount i+1 := by
  have hle : D.blockCount (i+D.v) ≤ D.blockCount i+1 := by
    apply (D.blockCount_le_iff _ _).mpr
    nlinarith [D.index_le_blocks i]
  by_cases hz : i=0
  · subst i;simpa only [zero_add,D.blockCount_zero,zero_add] using D.blockCount_v
  apply le_antisymm hle
  by_contra hn
  have hb : D.blockCount (i+D.v) ≤ D.blockCount i := by omega
  have hmul := Nat.mul_le_mul_left D.v hb
  have hs := D.index_le_blocks (i+D.v)
  have hp := D.blockCount_pred_bound (show 0 < i by omega)
  have he := Nat.sub_add_cancel (show 1 ≤ D.blockCount i from D.blockCount_pos (by omega))
  nlinarith only [hmul,hs,hp,he]
end NSP14.ArithmeticSequence.Data
