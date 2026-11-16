module
public import NSP14.Ordinary.CutResidualModule
public import NSP14.ArithmeticSequence.Interval
public import tests.TowerHarmonic
public import Mathlib.Algebra.Field.ZMod
@[expose] public section
open CategoryTheory NSP14 NSP14.Homological NSP14.NumericalSemigroup
namespace CutResidualAcceptance
abbrev L := InfiniteScalarField (ZMod 2)
def D : ArithmeticSequence.Data := ArithmeticSequence.intervalData 5 4 (by decide) (by decide)

theorem embedding : D.source.embeddingDimension=5 := by rw [D.embeddingDimension];rfl
theorem deficit_zero : D.source.deficit=0 := by
  rw [deficit,D.multiplicity,embedding]
  rfl

theorem cut_rank : D.source.actualCutRank=2 := by
  have h := D.source.degree_two_le_deficit
  rw [deficit_zero] at h
  have hz : (D.source.degreeSet 2).card=0 := by omega
  rw [actualCutRank,hz]
  decide

noncomputable def C : D.source.LinearCutData L := D.source.infiniteFieldCut (ZMod 2) (by rw [embedding];decide)

theorem complement : C.complementRank=2 := by
  rw [C.complementRank_eq,embedding,cut_rank]

/-- Actual cut quotient with two surviving complement variables, over the
same characteristic-two extension used for the cut. -/
theorem actual_Z_action : C.cutResidualEquiv.toAlgHom.comp C.complementPolynomialToResidual=
    firstOrderPolynomial L C.complementRank 0 := C.cutResidual_Z_action

theorem actual_B_model : Nonempty (C.cutB ≅ firstOrderModule L D.source.actualCutRank C.complementRank) :=
  ⟨C.cutBModelIso⟩

theorem actual_Z_unit (i : Fin C.complementRank) :
    C.cutResidualEquiv (C.complementPolynomialToResidual (MvPolynomial.X i))=
      TrivSqZeroExt.inr (Pi.single i (1:L)) := by
  change C.cutResidualEquiv (Ideal.Quotient.mk (D.source.linearCutIdeal L C.forms D.source.actualCutRank)
    (C.complementPolynomialToA (MvPolynomial.X i)))=_
  rw [C.cutResidualEquiv_mk,C.complementPolynomialToA_X,C.headToResidual_complement]

theorem actual_Z_nonzero (i : Fin C.complementRank) : C.complementPolynomialToResidual (MvPolynomial.X i)≠0 := by
  intro hz
  have h := actual_Z_unit i
  rw [hz,map_zero] at h
  have hc := congrArg (fun a : TrivSqZeroExt L (Fin C.complementRank → L) => a.snd i) h
  simp at hc

theorem actual_Z_betti_one :
    letI := C.cutResidualModule_finite
    totalBetti L (Fin C.complementRank) C.cutResidualModule 1=3 := by
  let := C.cutResidualModule_finite
  rw [C.cutResidual_Z_betti 1 (by decide),complement]
  norm_num

theorem actual_Z_betti_two :
    letI := C.cutResidualModule_finite
    totalBetti L (Fin C.complementRank) C.cutResidualModule 2=2 := by
  let := C.cutResidualModule_finite
  rw [C.cutResidual_Z_betti 2 (by decide),complement]
  norm_num

noncomputable abbrev C0 := TowerHarmonicAcceptance.rankTwoCut

theorem complement_zero : C0.complementRank=0 := by
  rw [C0.complementRank_eq,Run14Fixtures.rankTwo.embedding,Run14Fixtures.rankTwo.cut_rank]

theorem actual_empty_Z (i : ℕ) (hi : 1 ≤ i) :
    letI := C0.cutResidualModule_finite
    totalBetti L (Fin C0.complementRank) C0.cutResidualModule i=0 := by
  let := C0.cutResidualModule_finite
  rw [C0.cutResidual_Z_betti i hi,complement_zero]
  have hc : (1 : ℕ).choose (i+1)=0 := Nat.choose_eq_zero_of_lt (by omega)
  simp [hc]

end CutResidualAcceptance
