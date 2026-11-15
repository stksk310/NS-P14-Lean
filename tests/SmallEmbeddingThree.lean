module
import tests.LTVActual
open NSP14 NSP14.Tests.Run19Three
example (k : Type) [Field k] (i : ℕ) :=
  SmallEmbedding.three_comparison narrowNonCM.source k nonCM_embedding i
example (k : Type) [Field k] (i : ℕ) :=
  SmallEmbedding.three_comparison cm.source k (by rw [cm.embeddingDimension];rfl) i
example (k : Type) [Field k] (i : ℕ) := SmallEmbedding.three_comparison boundaryWide.source k
  (by rw [boundaryWide.embeddingDimension];rfl) i
example := SmallEmbedding.three_comparison narrowNonCM.source ℚ nonCM_embedding 0
example := SmallEmbedding.three_comparison narrowNonCM.source (ZMod 2) nonCM_embedding 1
example := SmallEmbedding.three_comparison narrowNonCM.source (ZMod 3) nonCM_embedding 2
example := SmallEmbedding.three_comparison narrowNonCM.source (ZMod 2) nonCM_embedding 3
example := SmallEmbedding.three_comparison narrowNonCM.source (ZMod 3) nonCM_embedding 4
