module
public import NSP14.ArithmeticSequence.Apery
public import NSP14.ArithmeticSequence.MaximalEmbeddingBetti
@[expose] public section
namespace NSP14.ArithmeticSequence.Data
variable (D : NSP14.ArithmeticSequence.Data)

/-- The actual ordinary cone used as the auxiliary algebra. Its
multiplicity is v, and its embedding dimension is v. -/
def ordinaryModel (hv : 2 ≤ D.v) : NSP14.ArithmeticSequence.Data where
  m := D.v
  d := 1
  v := D.v-1
  m_two := hv
  d_pos := by decide
  v_pos := by omega
  v_lt := by omega
  coprime := Nat.coprime_one_right _

theorem ordinaryModel_mem (hv : 2 ≤ D.v) (x : ℕ) :
    x ∈ (D.ordinaryModel hv).source ↔ x=0 ∨ D.v ≤ x := by
  constructor
  · intro hx
    by_cases hz : x=0
    · exact Or.inl hz
    · right
      have h := (D.ordinaryModel hv).source.multiplicity_le hx (by omega)
      rw [(D.ordinaryModel hv).multiplicity] at h
      exact h
  · rintro (rfl|hx)
    · exact (D.ordinaryModel hv).source.zero_mem
    · have hn : 1 ≤ x/D.v := Nat.div_pos hx (by omega)
      have hj : x%D.v < D.v := Nat.mod_lt _ (by omega)
      refine ⟨x/D.v,x%D.v,?_,?_⟩
      · change x%D.v ≤ (D.v-1)*(x/D.v)
        nlinarith [Nat.sub_add_cancel (show 1 ≤ D.v by omega)]
      · change x=x/D.v*D.v+x%D.v*1
        simpa only [Nat.mul_one,Nat.mul_comm,Nat.add_comm] using (Nat.mod_add_div x D.v).symm

theorem ordinaryModel_order (hv : 2 ≤ D.v) {x : ℕ}
    (hx : x ∈ (D.ordinaryModel hv).source) :
    (D.ordinaryModel hv).source.order x=x/D.v := by
  rcases (D.ordinaryModel_mem hv x).mp hx with rfl|hx'
  · simp [(D.ordinaryModel hv).source.order_zero]
  have hn : 1 ≤ x/D.v := Nat.div_pos hx' (by omega)
  have hj : x%D.v < D.v := Nat.mod_lt _ (by omega)
  have hi : x%D.v ≤ (D.v-1)*(x/D.v) := by
    nlinarith [Nat.sub_add_cancel (show 1 ≤ D.v by omega)]
  have he : x=x/D.v*D.v+x%D.v*1 := by
    simpa only [Nat.mul_one,Nat.mul_comm,Nat.add_comm] using (Nat.mod_add_div x D.v).symm
  calc
    (D.ordinaryModel hv).source.order x=
        (D.ordinaryModel hv).source.order (x/D.v*D.v+x%D.v*1) := congrArg _ he
    _=x/D.v := (D.ordinaryModel hv).canonical_order _ _ hj hi
end NSP14.ArithmeticSequence.Data
