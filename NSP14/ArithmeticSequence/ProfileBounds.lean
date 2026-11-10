module
public import NSP14.ArithmeticSequence.BettiFormula
@[expose] public section
namespace NSP14.Target

def apLowerProfile (v i : ℕ) : ℕ :=
  i*v.choose (i+1)+min (v.choose (i-1)) (v.choose i)

theorem apLowerProfile_monotone (i : ℕ) : Monotone (fun v => apLowerProfile v i) := by
  intro a b h
  exact Nat.add_le_add (Nat.mul_le_mul_left i (Nat.choose_le_choose (i+1) h))
    (min_le_min (Nat.choose_le_choose (i-1) h) (Nat.choose_le_choose i h))
end NSP14.Target
namespace NSP14.ArithmeticSequence.Data
variable (D : NSP14.ArithmeticSequence.Data)

/-- The 1..v residue convention in m=a*v+b, including b=v. -/
def blockResidue : ℕ := (D.m-1)%D.v+1

theorem blockResidue_pos : 1 ≤ D.blockResidue := by unfold blockResidue;omega

theorem blockResidue_le : D.blockResidue ≤ D.v := by
  have h := Nat.mod_lt (D.m-1) (show 0 < D.v from D.v_pos)
  unfold blockResidue
  omega

theorem multiplicity_blocks : D.m=((D.m-1)/D.v)*D.v+D.blockResidue := by
  have h := Nat.mod_add_div (D.m-1) D.v
  have hp := Nat.sub_add_cancel (show 1 ≤ D.m by have := D.m_two;omega)
  unfold blockResidue
  nlinarith only [h,hp]

theorem residueDefect_eq_blockResidue : D.residueDefect=D.v-D.blockResidue+1 := by
  have h := D.blockResidue_le
  unfold residueDefect blockResidue at *
  omega


theorem positiveBettiProfile_lower (i : ℕ) :
    NSP14.Target.apLowerProfile D.v i ≤ D.positiveBettiProfile i := by
  unfold NSP14.Target.apLowerProfile positiveBettiProfile
  apply Nat.add_le_add_left
  by_cases h : i≤D.residueDefect
  · rw [ite_eq_left h]
    calc
      min (D.v.choose (i-1)) (D.v.choose i) ≤ D.v.choose (i-1) := min_le_left _ _
      _≤(D.residueDefect+1-i)*D.v.choose (i-1) := by
        have hc : 1 ≤ D.residueDefect+1-i := by omega
        simpa only [one_mul] using Nat.mul_le_mul_right (D.v.choose (i-1)) hc
  · rw [ite_eq_right h]
    calc
      min (D.v.choose (i-1)) (D.v.choose i) ≤ D.v.choose i := min_le_right _ _
      _≤(i-D.residueDefect)*D.v.choose i := by
        have hc : 1 ≤ i-D.residueDefect := by omega
        simpa only [one_mul] using Nat.mul_le_mul_right (D.v.choose i) hc

theorem positiveBettiProfile_above (i : ℕ) (hi : D.v < i) : D.positiveBettiProfile i=0 := by
  have hD := D.residueDefect_le
  unfold positiveBettiProfile
  rw [ite_eq_right (show ¬i≤D.residueDefect by omega),
    Nat.choose_eq_zero_of_lt (show D.v < i+1 by omega),Nat.choose_eq_zero_of_lt hi]
  simp

variable (k : Type) [Field k]

theorem semigroup_totalBetti_above (i : ℕ) (hi : D.v < i) :
    NSP14.Homological.totalBetti k D.source.AtomExponent
      (ModuleCat.of (D.source.FullPolynomialRing k) (D.source.SemigroupRing k)) i=0 := by
  rw [D.semigroup_totalBetti_pos k i (by have := D.v_pos;omega),D.positiveBettiProfile_above i hi]
end NSP14.ArithmeticSequence.Data
