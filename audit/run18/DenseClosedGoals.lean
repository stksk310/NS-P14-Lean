module
public import audit.run18.DenseResourcesClosed
public import NSP14.Width.DenseComparison
@[expose] public section
namespace NSP14.Run18
/-- The original dense resources and literal-source first-term/completion closure. -/
theorem dense_closed : Requested.W_DENSE := by
  constructor
  · exact dense_resources_closed
  · intro S k _ he hw
    dsimp only
    intro t hu ht2 htq
    exact ⟨fun i hi => S.narrow_dense_firstterm k he hw t hu ht2 htq i hi,
      fun i => S.narrow_dense_comparison k he hw t hu ht2 htq i⟩
end NSP14.Run18
