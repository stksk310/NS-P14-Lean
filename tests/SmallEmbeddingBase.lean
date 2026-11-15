module
import NSP14.SmallEmbedding.Base
import Mathlib.Algebra.Field.ZMod
open NSP14 NSP14.Homological
open scoped Classical
namespace NSP14.Tests.Run19Base

def naturals : NumericalSemigroup where
  carrier := ⊤
  conductor := 0
  cofinite := by intros;trivial

theorem naturals_atoms : naturals.atoms={1} := by
  ext x
  rw [naturals.mem_atoms_iff,Finset.mem_singleton]
  constructor
  · intro hx
    have hp := hx.2.1
    have h := hx.2.2 1 (by trivial) (x-1) (by trivial) (by omega)
    omega
  · rintro rfl
    refine ⟨by trivial,by omega,?_⟩
    intro u _ v _ h
    omega

theorem naturals_embedding : naturals.embeddingDimension=1 := by
  change naturals.atoms.card=1
  rw [naturals_atoms,Finset.card_singleton]

theorem naturals_width_zero : naturals.width=0 := by
  have h := SmallEmbedding.one_atom naturals naturals_embedding
  rw [NumericalSemigroup.width,h.2.1,h.2.2.1]

def twoThree : ArithmeticSequence.Data where
  m := 2
  d := 1
  v := 1
  m_two := by decide
  d_pos := by decide
  v_pos := by decide
  v_lt := by decide
  coprime := by decide

def threeFive : ArithmeticSequence.Data where
  m := 3
  d := 2
  v := 1
  m_two := by decide
  d_pos := by decide
  v_pos := by decide
  v_lt := by decide
  coprime := by decide

example (k : Type) [Field k] (i : ℕ) :
    totalBetti k naturals.AtomExponent
      (ModuleCat.of (naturals.FullPolynomialRing k) (naturals.FormalTangentAlgebra k)) i=
        if i=0 then 1 else 0 := SmallEmbedding.one_completed_betti naturals naturals_embedding k i
example := SmallEmbedding.one_completed_betti naturals naturals_embedding ℚ 1
example := SmallEmbedding.one_completed_betti naturals naturals_embedding (ZMod 2) 2
example := SmallEmbedding.one_completed_betti naturals naturals_embedding (ZMod 3) 0
example := SmallEmbedding.one_literal_carrier naturals naturals_embedding
example (k : Type) [Field k] (i : ℕ) := SmallEmbedding.two_completed_betti twoThree.source
  (by rw [twoThree.embeddingDimension];rfl) k i
example (k : Type) [Field k] (i : ℕ) := SmallEmbedding.two_completed_betti threeFive.source
  (by rw [threeFive.embeddingDimension];rfl) k i
example := SmallEmbedding.base_comparison threeFive.source (ZMod 2)
  (by rw [threeFive.embeddingDimension];decide) 3
example := SmallEmbedding.base_comparison twoThree.source (ZMod 3)
  (by rw [twoThree.embeddingDimension];decide) 1
end NSP14.Tests.Run19Base
