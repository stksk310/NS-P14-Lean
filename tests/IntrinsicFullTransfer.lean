module
public import NSP14.Ordinary.NumericalBettiClosure
public import tests.ActualTorRow
public import tests.CutResidual
@[expose] public section
open NSP14 NSP14.Homological
namespace IntrinsicFullTransferAcceptance
abbrev L := InfiniteScalarField (ZMod 2)
noncomputable abbrev W2 := ActualTorRowAcceptance.W2
noncomputable abbrev W3 := ActualTorRowAcceptance.W3
noncomputable def W5 : Ordinary.ActualWitness (ZMod 2) :=
  ⟨CutResidualAcceptance.D.source,(by rw [CutResidualAcceptance.embedding];decide),CutResidualAcceptance.C⟩

theorem complement_two : W5.cut.complementRank=2 := CutResidualAcceptance.complement

theorem actual_intrinsic_transfer (i : ℕ) (hi : 1 ≤ i) :
    letI := W5.relativeG_finite
    let f := W5.source.embeddingDimension-W5.source.actualCutRank-1
    (totalBetti L W5.source.AtomExponent (ModuleCat.of (W5.source.FullPolynomialRing L)
      (W5.source.TangentAlgebra L)) i : ℚ) ≤
      Target.positiveOrdinaryCoefficient (f+1) i+
        ∑ j∈Finset.range i,(f.choose (i-(j+1)) : ℚ)*
          totalBetti L (Option (Fin W5.source.actualCutRank)) W5.relativeG (j+1) := W5.correctedFullTransfer i hi

theorem actual_source_all_rows (i : ℕ) (hi : 1 ≤ i) :
    totalBetti (ZMod 2) W3.source.AtomExponent
      (ModuleCat.of (W3.source.FullPolynomialRing (ZMod 2)) (W3.source.TangentAlgebra (ZMod 2))) i ≤
        i*W3.source.multiplicity.choose (i+1) :=
  Ordinary.ordinary_betti_bound W3.source (ZMod 2) W3.embedding i hi

theorem actual_rank_two_top_preserved :
    letI := W2.relativeG_finite
    bettiEuler L (Option (Fin W2.source.actualCutRank)) W2.relativeG (W2.source.actualCutRank+1)=0 :=
  W2.relative_Euler_terminal
end IntrinsicFullTransferAcceptance
