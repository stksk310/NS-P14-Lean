module
public import NSP14.Main.IntervalTarget
public import NSP14.Main.Partition
@[expose] public section
namespace NSP14.Run20.Requested
open NSP14.Homological

def I_PARTITION : Prop := ∀ (S : NumericalSemigroup),
  (∃! j : Fin 6, S.parameterRegion j) ∧
  (4 ≤ S.embeddingDimension → S.cutParameters) ∧
  ∀ (he : 4 ≤ S.embeddingDimension) (hw : S.width ≤ S.multiplicity-2),
    S.narrowParameters he hw

def I_MAIN : Prop :=
  ∀ (S : NumericalSemigroup) (k : Type) [Field k] (i : ℕ),
    let T := S.intervalCompletionAll
    totalBetti k S.AtomExponent
      (ModuleCat.of (S.FullPolynomialRing k) (S.FormalTangentAlgebra k)) i ≤
    totalBetti k T.AtomExponent
      (ModuleCat.of (T.FullPolynomialRing k) (T.FormalTangentAlgebra k)) i
end NSP14.Run20.Requested
