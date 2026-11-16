module
public import NSP14.SmallEmbedding.ThreeComparison
public import Mathlib.Algebra.Field.ZMod
@[expose] public section
open scoped Classical
open NSP14 NSP14.Homological
namespace NSP14.Tests.Run19Three

def narrowNonCM : SmallEmbedding.ThreeData where
  m := 8
  d := 1
  u := 6
  a := {1}
  q_one := by decide
  a_pos := by intro b hb;simp only [Finset.mem_singleton] at hb;omega
  a_lt := by intro b hb;simp only [Finset.mem_singleton] at hb;omega
  u_lt := by decide
  d_pos := by decide
  offsets_coprime := by decide
  coprime := by decide

def cm : SmallEmbedding.ThreeData where
  m := 5
  d := 1
  u := 3
  a := {1}
  q_one := by decide
  a_pos := by intro b hb;simp only [Finset.mem_singleton] at hb;omega
  a_lt := by intro b hb;simp only [Finset.mem_singleton] at hb;omega
  u_lt := by decide
  d_pos := by decide
  offsets_coprime := by decide
  coprime := by decide

def boundaryWide : ArithmeticSequence.Data where
  m := 3
  d := 1
  v := 2
  m_two := by decide
  d_pos := by decide
  v_pos := by decide
  v_lt := by decide
  coprime := by decide

theorem nonCM_embedding : narrowNonCM.source.embeddingDimension=3 := by
  rw [narrowNonCM.embeddingDimension];rfl
example (k : Type) [Field k] : narrowNonCM.coreP k ≤ 6 :=
  narrowNonCM.one_coreP_bound k rfl
example (k : Type) [Field k] : narrowNonCM.actualR k ≤ 3 :=
  narrowNonCM.actualR_one_bound k rfl
example (k : Type) [Field k] : cm.actualR k=0 := by
  have h := cm.actualR_one_bound k rfl
  change cm.actualR k ≤ 0 at h
  omega
example := narrowNonCM.actualR_one_bound ℚ rfl
example := narrowNonCM.actualR_one_bound (ZMod 2) rfl
example := narrowNonCM.actualR_one_bound (ZMod 3) rfl
example := narrowNonCM.minimalEncoding_injective
example := narrowNonCM.positive_minimal_witness
example := SmallEmbedding.one_first_payment 3 (by decide)
example := SmallEmbedding.one_second_payment 3 (by decide)
end NSP14.Tests.Run19Three
