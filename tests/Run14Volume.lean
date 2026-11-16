module
public import NSP14
@[expose] public section
namespace Run14Volume
open NSP14 NSP14.NumericalSemigroup
open scoped BigOperators Classical
theorem sharp_volume (S : NumericalSemigroup) :
    (∑ r ∈ (Finset.univ : Finset (Fin S.multiplicity)).filter (fun r => r.val ≠ 0),
      ((S.offsetLevel r - 1 : ℕ) : ℚ)) ≤
    (S.deficit : ℚ) * NSP14.Ordinary.SmallScalar.volume S.embeddingDimension S.deficit :=
  S.offset_volume_bound

end Run14Volume
