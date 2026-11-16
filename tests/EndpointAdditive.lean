module
public import NSP14.Additive.EndpointDistance
public import NSP14.Additive.QuadraticVolume
public import NSP14.Additive.StandardWordSequence
public import NSP14.Endpoint.FiniteMinima
public import Mathlib.Algebra.Field.ZMod
@[expose] public section
open scoped Pointwise Classical
set_option maxRecDepth 4096
open NSP14.Endpoint
theorem Run17_distance_contract (D : Data) (n : ℕ) (r : ZMod D.u) :
    r ∈ NSP14.Additive.iteratedSum D.residueAlphabet n ↔
      D.shortestDegree (D.residueIndex r) ≤ n := D.residue_distance_iff n r

namespace Run17Endpoint
def dilated : Data where
  m := 7
  d := 2
  u := 4
  a := {1,3}
  q_two := by decide
  a_pos := by decide
  a_lt := by decide
  u_lt := by decide
  d_pos := by decide
  offsets_coprime := by decide
  coprime := by decide
def volume : Data where
  m := 8
  d := 1
  u := 6
  a := {2,3}
  q_two := by decide
  a_pos := by decide
  a_lt := by decide
  u_lt := by decide
  d_pos := by decide
  offsets_coprime := by decide
  coprime := by decide
def survivor : Data where
  m := 9
  d := 1
  u := 7
  a := {2,3}
  q_two := by decide
  a_pos := by decide
  a_lt := by decide
  u_lt := by decide
  d_pos := by decide
  offsets_coprime := by decide
  coprime := by decide
def word : Fin 2 → survivor.a := ![⟨2,by decide⟩,⟨3,by decide⟩]
theorem normalized_alphabet : dilated.residueAlphabet.card=3 := by decide
theorem physical_alphabet_loses_residues :
    (dilated.a.image (fun a : ℕ => (dilated.d*a : ZMod dilated.u)))={2} := by decide
theorem actual_volume : volume.wordVolume=10 := by
  rw [volume.wordVolume_tail]
  decide
theorem actual_volume_bound : volume.wordVolume ≤ 1+(volume.u*volume.u)/4 :=
  volume.wordVolume_two_bound rfl
theorem actual_survivor_minimal : survivor.CoreMinimal (survivor.indexedInternalWord word) := by
  apply (survivor.computedMinima_iff _ _).mp
  decide
theorem actual_survivor_nonzero (k : Type) [Field k] :
    Ideal.Quotient.mk (NSP14.Endpoint.endpointIdeal k (survivor.Core k) (survivor.endpointToCore k))
      (survivor.coreMonomial k (survivor.indexedInternalWord word)) ≠ 0 := by
  rw [survivor.QCore_class_monomial,dite_eq_left actual_survivor_minimal]
  exact Module.Basis.ne_zero _ _
theorem actual_survivor_zeroSumFree :
    NSP14.Additive.ZeroSumFree (survivor.internalWordSequence word) :=
  survivor.surviving_internal_word_zeroSumFree (ZMod 2) word (actual_survivor_nonzero (ZMod 2))
end Run17Endpoint
