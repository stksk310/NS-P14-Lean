module
public import NSP14.ArithmeticSequence.ModelTorClosure
public import NSP14.ArithmeticSequence.TwoGeneratorBetti
public import NSP14.ArithmeticSequence.ConeBetti
public import NSP14.Homological.InfiniteScalarField
@[expose] public section
open NSP14.Homological
namespace NSP14.ArithmeticSequence.Data
variable (D : NSP14.ArithmeticSequence.Data)

/-- The positive quotient-Betti profile, with the residue endpoint
D=v−((m−1) mod v). It is only a numerical definition. -/
def positiveBettiProfile (i : ℕ) : ℕ :=
  i*D.v.choose (i+1)+
    if i≤D.residueDefect then (D.residueDefect+1-i)*D.v.choose (i-1)
    else (i-D.residueDefect)*D.v.choose i

theorem positiveBettiProfile_v_one (hv : D.v=1) (i : ℕ) (hi : 1 ≤ i) :
    D.positiveBettiProfile i=if i=1 then 1 else 0 := by
  have hD : D.residueDefect=1 := by unfold residueDefect;rw [hv,Nat.mod_one]
  by_cases he : i=1
  · subst i;simp [positiveBettiProfile,hv,hD]
  · have hit : 1 < i := by omega
    rw [ite_eq_right he]
    unfold positiveBettiProfile
    rw [hv,hD,ite_eq_right (show ¬i≤1 by omega),
      Nat.choose_eq_zero_of_lt (show 1 < i+1 by omega),Nat.choose_eq_zero_of_lt hit]
    simp

variable (k : Type) [Field k]

/-- The actual full-minimal AP cone Betti formula for every original
field, all positive rows, and every permitted common difference. -/
theorem cone_totalBetti_pos (i : ℕ) (hi : 1 ≤ i) :
    totalBetti k D.source.AtomExponent
      (ModuleCat.of (D.source.FullPolynomialRing k) (D.source.TangentAlgebra k)) i=
        D.positiveBettiProfile i := by
  by_cases hv : D.v=1
  · rw [D.positiveBettiProfile_v_one hv i hi]
    by_cases he : i=1
    · subst i;rw [ite_eq_left rfl];exact D.twoGenerator_cone_betti_one k hv
    · rw [ite_eq_right he]
      exact D.twoGenerator_cone_betti_above k hv i (by omega)
  · have hv2 : 2 ≤ D.v := by have := D.v_pos;omega
    have h := D.apCone_betti_infinite hv2 (InfiniteScalarField k) i hi
    rw [D.source.actualG_totalBetti_baseChange k (InfiniteScalarField k) i] at h
    exact h

/-- The GSS positive formula on the actual algebraic semigroup ring.
The equality with the cone is separately proved on actual modules. -/
theorem semigroup_totalBetti_pos (i : ℕ) (hi : 1 ≤ i) :
    totalBetti k D.source.AtomExponent
      (ModuleCat.of (D.source.FullPolynomialRing k) (D.source.SemigroupRing k)) i=
        D.positiveBettiProfile i := by
  rw [D.semigroup_cone_totalBetti k,D.cone_totalBetti_pos k i hi]

theorem semigroup_totalBetti_zero :
    totalBetti k D.source.AtomExponent
      (ModuleCat.of (D.source.FullPolynomialRing k) (D.source.SemigroupRing k)) 0=1 := by
  rw [D.semigroup_cone_totalBetti k,D.source.actualG_totalBetti_zero]

/-- The ordinary quotient table includes its actual zeroth row. -/
def bettiProfile (i : ℕ) : ℕ := if i=0 then 1 else D.positiveBettiProfile i

theorem cone_totalBetti (i : ℕ) :
    totalBetti k D.source.AtomExponent
      (ModuleCat.of (D.source.FullPolynomialRing k) (D.source.TangentAlgebra k)) i=D.bettiProfile i := by
  by_cases hi : i=0
  · subst i;rw [D.source.actualG_totalBetti_zero];rfl
  · rw [bettiProfile,ite_eq_right hi]
    exact D.cone_totalBetti_pos k i (by omega)

theorem semigroup_totalBetti (i : ℕ) :
    totalBetti k D.source.AtomExponent
      (ModuleCat.of (D.source.FullPolynomialRing k) (D.source.SemigroupRing k)) i=D.bettiProfile i := by
  rw [D.semigroup_cone_totalBetti k,D.cone_totalBetti k i]

theorem completed_AP_totalBetti (i : ℕ) :
    totalBetti k D.source.AtomExponent
      (ModuleCat.of (D.source.FullPolynomialRing k) (D.source.FormalTangentAlgebra k)) i=D.bettiProfile i := by
  rw [← D.source.completed_totalBetti k,D.cone_totalBetti k i]
end NSP14.ArithmeticSequence.Data
