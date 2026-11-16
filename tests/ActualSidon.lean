module
import NSP14.Semigroup.ActualSidon
open NSP14
open NSP14.NumericalSemigroup
example (S : NumericalSemigroup) (k : Type) [Field k]
    (ha : Module.finrank k (S.qDegree k 2) = S.embeddingDimension.choose 2) :
    S.embeddingDimension * (S.embeddingDimension - 1) + 1 ≤ S.multiplicity :=
  S.maximal_qDegree_multiplicity_bound k ha
