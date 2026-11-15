module
public import audit.run19.ClosedN4Goals
public import NSP14.SmallEmbedding.Base
@[expose] public section
namespace NSP14.Run19
theorem base_closed : Requested.I_BASE := by
  intro S k _ he i
  exact SmallEmbedding.base_comparison S k he i
end NSP14.Run19
