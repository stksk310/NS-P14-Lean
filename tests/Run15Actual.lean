module
public import NSP14
public import tests.Run14Closure
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open NSP14 NSP14.NumericalSemigroup NSP14.Ordinary NSP14.Homological
open scoped BigOperators
namespace Run15Actual

def genuineAP : ArithmeticSequence.Data where
  m := 5
  d := 2
  v := 3
  m_two := by decide
  d_pos := by decide
  v_pos := by decide
  v_lt := by decide
  coprime := by decide

def rankOneAP : ArithmeticSequence.Data where
  m := 4
  d := 3
  v := 1
  m_two := by decide
  d_pos := by decide
  v_pos := by decide
  v_lt := by decide
  coprime := by decide

def maximalAP : ArithmeticSequence.Data where
  m := 5
  d := 1
  v := 4
  m_two := by decide
  d_pos := by decide
  v_pos := by decide
  v_lt := by decide
  coprime := by decide

theorem genuine_minimal : genuineAP.source.embeddingDimension=4 := genuineAP.embeddingDimension

theorem genuine_order : genuineAP.source.order 18=2 :=
  genuineAP.canonical_order 2 4 (by decide) (by decide)

theorem rank_one_order : rankOneAP.source.order 21=3 :=
  rankOneAP.canonical_order 3 3 (by decide) (by decide)

theorem genuine_apery_top : 18 ∈ genuineAP.source.aperySet := genuineAP.aperyValue_mem (i:=4) (by decide)

theorem maximal_apery : 9 ∈ maximalAP.source.aperySet := maximalAP.aperyValue_mem (i:=4) (by decide)

theorem genuine_char_two_regular : Function.Injective (genuineAP.source.xMultiply (ZMod 2)) :=
  genuineAP.xMultiply_injective (ZMod 2)

theorem actual_rank_two_R_finite :
    Module.Finite Run14Closure.rankTwoWitness.RelativeRing Run14Closure.rankTwoWitness.relativeG :=
  Run14Closure.rankTwoWitness.relativeG_finite

theorem actual_rank_three_relative_embedding : Function.Injective Run14Closure.rankThreeWitness.relativeToFull :=
  Run14Closure.rankThreeWitness.relativeToFull_injective

theorem same_rank_three_tower (s j : ℕ) (hs : 1 ≤ s) :
    Run14Closure.rankThreeWitness.cut.cutKEuler s j ≤
      Run14Closure.rankThreeWitness.cut.cutHighEuler s (s+1) j+
      Run14Closure.rankThreeWitness.cut.cutHighEuler (s+1) (s+1) (j+1) :=
  Run14Closure.rankThreeWitness.cut.cutTower_kernel_le s hs j

theorem actual_T_filtration (j : ℕ) :
    Run14Closure.rankThreeWitness.cut.cutTEuler j ≤
      ∑ t ∈ Finset.range (Run14Fixtures.rankThree.source.qTopDegree-1),
        Run14Closure.rankThreeWitness.cut.cutKEuler (2+t) j :=
  Run14Closure.rankThreeWitness.cut.cutTEuler_le_sum j

theorem finite_length_top :
    Run14Closure.rankThreeWitness.cut.cutHighEuler 2 2 Run14Fixtures.rankThree.source.actualCutRank=0 :=
  Run14Closure.rankThreeWitness.cut.cutHighEuler_top 2 2

theorem free_is_not_universally_nonnegative :
    bettiEuler (ZMod 2) (Fin 2) (ModuleCat.of
      (VariableRing (ZMod 2) (Fin 2)) (VariableRing (ZMod 2) (Fin 2))) 1 = -1 :=
  bettiEuler_free_one (ZMod 2) (Fin 2)

/-- A genuine nonzero connecting correction on an actual polynomial-module
short exact sequence. Its two free chain inputs are infinite over k. -/
theorem nonzero_connecting (k : Type) [Field k] :
    let f : VariableRing k Unit := MvPolynomial.X ()
    koszulCorrectionRank k Unit (principalSequence k Unit f)
      (principal_shortExact k Unit f (MvPolynomial.X_ne_zero ())) 0=1 := by
  dsimp only
  let f : VariableRing k Unit := MvPolynomial.X ()
  have hf : f ≠ 0 := MvPolynomial.X_ne_zero ()
  have hm : f ∈ variablesIdeal k Unit (variableList k Unit) :=
    Ideal.subset_span ⟨(),mem_variableList k Unit (),rfl⟩
  have hb := (principal_totalBetti k Unit f hf hm).1
  let : Module.Finite (VariableRing k Unit) (principalSequence k Unit f).X₁ :=
    inferInstanceAs (Module.Finite (VariableRing k Unit) (VariableRing k Unit))
  let : Module.Finite (VariableRing k Unit) (principalSequence k Unit f).X₂ :=
    inferInstanceAs (Module.Finite (VariableRing k Unit) (VariableRing k Unit))
  let : Module.Finite (VariableRing k Unit) (principalSequence k Unit f).X₃ := principal_finite k Unit f
  have h := koszul_betti_rank_correction_zero k Unit (principalSequence k Unit f) (principal_shortExact k Unit f hf)
  change totalBetti k Unit (ModuleCat.of (VariableRing k Unit) (VariableRing k Unit)) 0+
    koszulCorrectionRank k Unit (principalSequence k Unit f) (principal_shortExact k Unit f hf) 0=
    totalBetti k Unit (ModuleCat.of (VariableRing k Unit) (VariableRing k Unit)) 0+
    totalBetti k Unit (principalModule k Unit f) 0 at h
  rw [hb,totalBetti_free_zero] at h
  change koszulCorrectionRank k Unit (principalSequence k Unit f) (principal_shortExact k Unit f hf) 0=1
  omega
theorem nonzero_connecting_char_two :
    let f : VariableRing (ZMod 2) Unit := MvPolynomial.X ()
    koszulCorrectionRank (ZMod 2) Unit (principalSequence (ZMod 2) Unit f)
      (principal_shortExact (ZMod 2) Unit f (MvPolynomial.X_ne_zero ())) 0=1 :=
  nonzero_connecting (ZMod 2)
end Run15Actual
