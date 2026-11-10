module

public import NSP14.Green.CutImage
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

@[expose] public section

open scoped Classical

namespace NSP14.Green

variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V]

def flagSpan {n : ℕ} (c : Fin n → V) (s : ℕ) : Submodule k V :=
  Submodule.span k (c '' {i | i.val < s})

@[simp] theorem flagSpan_full {n : ℕ} (c : Fin n → V) :
    flagSpan (k := k) c n = Submodule.span k (Set.range c) := by
  unfold flagSpan
  congr 1
  ext x
  simp only [Set.mem_image, Set.mem_ofPred_eq, Set.mem_range]
  constructor
  · rintro ⟨i,_,rfl⟩; exact ⟨i,rfl⟩
  · rintro ⟨i,rfl⟩; exact ⟨i,i.isLt,rfl⟩

@[simp] theorem flagSpan_zero {n : ℕ} (c : Fin n → V) : flagSpan (k := k) c 0 = ⊥ := by
  simp [flagSpan]

theorem flagSpan_snoc {n s : ℕ} (c : Fin n → V) (x : V) (hs : s ≤ n) :
    flagSpan (k := k) (Fin.snoc c x) s = flagSpan (k := k) c s := by
  unfold flagSpan
  congr 1
  ext z
  constructor
  · rintro ⟨i,hi,rfl⟩
    have hn : i.val < n := by exact lt_of_lt_of_le hi hs
    let j : Fin n := ⟨i.val,hn⟩
    have he : i = j.castSucc := Fin.ext rfl
    refine ⟨j,hi,?_⟩
    rw [he, Fin.snoc_castSucc]
  · rintro ⟨i,hi,rfl⟩
    exact ⟨i.castSucc,hi,by simp⟩

theorem flagSpan_snoc_full {n : ℕ} (c : Fin n → V) (x : V) :
    flagSpan (k := k) (Fin.snoc c x) (n + 1) = flagSpan (k := k) c n ⊔ Submodule.span k {x} := by
  rw [flagSpan_full, flagSpan_full, ← Submodule.span_union]
  congr 1
  ext z
  constructor
  · rintro ⟨i,rfl⟩
    refine Fin.lastCases ?_ ?_ i
    · exact Or.inr (by simp)
    · intro j
      exact Or.inl ⟨j,by simp⟩
  · rintro (hz | hz)
    · obtain ⟨i,rfl⟩ := hz
      exact ⟨i.castSucc,by simp⟩
    · have he : z = x := hz
      subst z
      exact ⟨Fin.last n,by simp⟩

end NSP14.Green
