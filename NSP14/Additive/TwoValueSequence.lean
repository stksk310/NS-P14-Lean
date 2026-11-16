module
public import NSP14.Additive.SavchevChen
@[expose] public section
open scoped BigOperators
namespace NSP14.Additive
def twoValueSequence {u : ℕ} (R T : ℕ) (α β : ZMod u) : Fin (R+T) → ZMod u :=
  Fin.addCases (fun _ => α) (fun _ => β)

theorem twoValue_representativeSum {u : ℕ} (R T : ℕ) (α β : ZMod u) (c : (ZMod u)ˣ) :
    representativeSum c (twoValueSequence R T α β) =
      R*((c : ZMod u)*α).val+T*((c : ZMod u)*β).val := by
  unfold representativeSum twoValueSequence
  rw [Fin.sum_univ_add]
  simp only [Fin.addCases_left,Fin.addCases_right,Finset.sum_const,Finset.card_univ,
    Fintype.card_fin,smul_eq_mul]

theorem normalized_modular_relation {u k : ℕ} [NeZero u] (c : (ZMod u)ˣ)
    (α β : ZMod u) (ha : ((c : ZMod u)*α).val = 1)
    (hb : ((c : ZMod u)*β).val = k) : (k : ZMod u)*α = β := by
  have ha' : (c : ZMod u)*α = 1 := by
    rw [←ZMod.natCast_zmod_val ((c : ZMod u)*α),ha,Nat.cast_one]
  have hb' : (c : ZMod u)*β = (k : ZMod u) := by
    rw [←ZMod.natCast_zmod_val ((c : ZMod u)*β),hb]
  have he : (c : ZMod u)*((k : ZMod u)*α) = (c : ZMod u)*β := by
    rw [mul_left_comm,ha',mul_one,hb']
  have hh := congrArg (fun x : ZMod u => (↑(c⁻¹) : ZMod u)*x) he
  simpa only [←mul_assoc,Units.inv_mul,one_mul] using hh

/-- The two-label consumer is derived from the general sequence theorem.
The disjunction explicitly records a possible swap of both labels and counts. -/
theorem savchevChen_twoValue {u R T : ℕ} (hu : 2 ≤ u) (hR : 1 ≤ R) (hT : 1 ≤ T)
    (α β : ZMod u) (hab : α ≠ β) (hz : ZeroSumFree (twoValueSequence R T α β))
    (hl : u < 2*(R+T)) :
    ∃ c : (ZMod u)ˣ, ∃ k : ℕ, 2 ≤ k ∧
      ((((c : ZMod u)*α).val = 1 ∧ ((c : ZMod u)*β).val = k ∧
          R+k*T ≤ u-1 ∧ (k : ZMod u)*α = β) ∨
       (((c : ZMod u)*β).val = 1 ∧ ((c : ZMod u)*α).val = k ∧
          T+k*R ≤ u-1 ∧ (k : ZMod u)*β = α)) := by
  let : NeZero u := ⟨by omega⟩
  obtain ⟨c,hpos,hbound⟩ := savchevChen_positive hu (twoValueSequence R T α β) hz hl
  have hpa := hpos (Fin.castAdd T ⟨0,by omega⟩)
  have hpb := hpos (Fin.natAdd R ⟨0,by omega⟩)
  simp only [twoValueSequence,Fin.addCases_left,Fin.addCases_right] at hpa hpb
  rw [twoValue_representativeSum] at hbound
  have hne : ((c : ZMod u)*α).val ≠ ((c : ZMod u)*β).val := by
    intro he
    have hh := congrArg (fun x : ZMod u => (↑(c⁻¹) : ZMod u)*x) (ZMod.val_injective u he)
    apply hab
    simpa only [←mul_assoc,Units.inv_mul,one_mul] using hh
  have hone : ((c : ZMod u)*α).val = 1 ∨ ((c : ZMod u)*β).val = 1 := by
    by_contra! hh
    have ha2 : 2 ≤ ((c : ZMod u)*α).val := by omega
    have hb2 : 2 ≤ ((c : ZMod u)*β).val := by omega
    have haR := Nat.mul_le_mul_left R ha2
    have hbT := Nat.mul_le_mul_left T hb2
    omega
  rcases hone with ha | hb
  · refine ⟨c,((c : ZMod u)*β).val,by omega,Or.inl ⟨ha,rfl,?_,?_⟩⟩
    · rw [ha,mul_one,mul_comm T] at hbound
      exact hbound
    · exact normalized_modular_relation c α β ha rfl
  · refine ⟨c,((c : ZMod u)*α).val,by omega,Or.inr ⟨hb,rfl,?_,?_⟩⟩
    · rw [hb,mul_one,mul_comm R] at hbound
      omega
    · exact normalized_modular_relation c β α hb rfl
end NSP14.Additive
