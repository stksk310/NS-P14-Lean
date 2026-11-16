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

namespace NSP14.Tests.Run19ThreeFullAP
def unitStep : ArithmeticSequence.Data where
  m := 4
  d := 1
  v := 2
  m_two := by decide
  d_pos := by decide
  v_pos := by decide
  v_lt := by decide
  coprime := by decide
def nonunitStep : ArithmeticSequence.Data where
  m := 7
  d := 2
  v := 2
  m_two := by decide
  d_pos := by decide
  v_pos := by decide
  v_lt := by decide
  coprime := by decide
example (k : Type) [Field k] (i : ℕ) := SmallEmbedding.three_comparison unitStep.source k
  (by rw [unitStep.embeddingDimension];rfl) i
example (k : Type) [Field k] (i : ℕ) := SmallEmbedding.three_comparison nonunitStep.source k
  (by rw [nonunitStep.embeddingDimension];rfl) i
example := SmallEmbedding.three_comparison nonunitStep.source (ZMod 2)
  (by rw [nonunitStep.embeddingDimension];rfl) 3
end NSP14.Tests.Run19ThreeFullAP
