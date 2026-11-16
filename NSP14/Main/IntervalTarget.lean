module
public import NSP14.SmallEmbedding.Base
@[expose] public section
open NSP14.Homological
namespace NSP14.NumericalSemigroup
variable (S : NumericalSemigroup)

/-- Carrier transport changes the minimal variable set as well as the algebra.
The conductor witness is deliberately not identified. -/
theorem carrier_completed_totalBetti (T : NumericalSemigroup) (h : S.carrier=T.carrier)
    (k : Type) [Field k] (i : ℕ) :
    totalBetti k S.AtomExponent
      (ModuleCat.of (S.FullPolynomialRing k) (S.FormalTangentAlgebra k)) i =
    totalBetti k T.AtomExponent
      (ModuleCat.of (T.FullPolynomialRing k) (T.FormalTangentAlgebra k)) i := by
  rw [←S.completed_totalBetti k,←T.completed_totalBetti k,S.carrier_totalBetti T h k i]

theorem intervalCompletionAll_completed_totalBetti (he : 2 ≤ S.embeddingDimension)
    (k : Type) [Field k] (i : ℕ) :
    totalBetti k S.intervalCompletionAll.AtomExponent
      (ModuleCat.of (S.intervalCompletionAll.FullPolynomialRing k)
        (S.intervalCompletionAll.FormalTangentAlgebra k)) i =
    totalBetti k (S.intervalCompletion he).AtomExponent
      (ModuleCat.of ((S.intervalCompletion he).FullPolynomialRing k)
        ((S.intervalCompletion he).FormalTangentAlgebra k)) i :=
  S.intervalCompletionAll.carrier_completed_totalBetti _ (S.intervalCompletionAll_carrier_eq he) k i

theorem intervalCompletionAll_one (he : S.embeddingDimension=1) :
    S.multiplicity=1 ∧ S.maxAtom=1 ∧ S.width=0 ∧
      S.intervalCompletionAll.carrier=AddSubmonoid.closure (Set.Icc 1 1) := by
  obtain ⟨_,hm,hmax,_⟩ := SmallEmbedding.one_atom S he
  exact ⟨hm,hmax,by rw [width,hm,hmax],by rw [S.intervalCompletionAll_carrier,hm,hmax]⟩
end NSP14.NumericalSemigroup
