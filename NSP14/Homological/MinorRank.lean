module

public import Mathlib.LinearAlgebra.Matrix.Rank

@[expose] public section

namespace NSP14.Homological

variable {ι m n : Type*} [Fintype ι] [DecidableEq ι]

/-- Integer ±1 determinants stay nonzero in every coefficient field, including characteristic two. -/
theorem signed_unit_determinant_ne_zero (k : Type*) [Field k] (B : Matrix ι ι ℤ)
    (hB : B.det=1 ∨ B.det = -1) : (B.map (Int.castRingHom k)).det≠0 := by
  have he : (B.map (Int.castRingHom k)).det = (Int.castRingHom k) B.det :=
    ((Int.castRingHom k).map_det B).symm
  rw [he]
  rcases hB with h | h <;> rw [h] <;> simp

/-- Finite-column rank comparison; finiteness is explicit, never inferred for an infinite chain group. -/
theorem nonzero_minor_rank_lower_bound (k : Type*) [Field k] [Fintype n]
    (A : Matrix m n k) (rows : ι → m) (cols : ι → n)
    (hminor : (A.submatrix rows cols).det≠0) : Fintype.card ι ≤ A.rank := by
  have h := Matrix.rank_submatrix_le A rows cols
  rw [Matrix.rank_of_det_ne_zero hminor] at h
  exact h

theorem signed_integer_minor_rank_lower_bound (k : Type*) [Field k] [Fintype n]
    (A : Matrix m n k) (rows : ι → m) (cols : ι → n) (B : Matrix ι ι ℤ)
    (hB : B.det=1 ∨ B.det = -1) (hmatch : A.submatrix rows cols=B.map (Int.castRingHom k)) :
    Fintype.card ι ≤ A.rank :=
  nonzero_minor_rank_lower_bound k A rows cols
    (hmatch ▸ signed_unit_determinant_ne_zero k B hB)

end NSP14.Homological
