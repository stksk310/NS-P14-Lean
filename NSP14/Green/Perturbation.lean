module

public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Algebra.Polynomial.Roots

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open scoped Classical

namespace NSP14.Green

variable {k V ι : Type*} [Field k] [Infinite k] [AddCommGroup V] [Module k V] [Fintype ι]

/-- A nonzero polynomial is nonzero at a nonzero point over an infinite field. -/
theorem exists_nonzero_eval (p : Polynomial k) (hp : p ≠ 0) :
    ∃ t : k, t ≠ 0 ∧ p.eval t ≠ 0 := by
  have hq : Polynomial.X * p ≠ 0 := mul_ne_zero Polynomial.X_ne_zero hp
  obtain ⟨t, ht⟩ : ∃ t : k, (Polynomial.X * p).eval t ≠ 0 := by
    by_contra hn
    push Not at hn
    apply hq
    apply Polynomial.funext
    intro t
    simpa using hn t
  have he : t * p.eval t ≠ 0 := by simpa using ht
  exact ⟨t, (mul_ne_zero_iff.mp he).1, (mul_ne_zero_iff.mp he).2⟩

/-- Independence persists at some nonzero point of any affine line. The proof
uses a determinant polynomial and is valid in characteristic two. -/
theorem generic_independent_line_avoiding (u v : ι → V) (hu : LinearIndependent k u)
    (p : Polynomial k) (hp : p ≠ 0) :
    ∃ t : k, t ≠ 0 ∧ p.eval t ≠ 0 ∧ LinearIndependent k (fun i => u i + t • v i) := by
  let f := Finsupp.linearCombination k u
  obtain ⟨g, hg⟩ := f.exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr hu.finsuppLinearCombination_injective)
  have hgu (j : ι) : g (u j) = Finsupp.single j 1 := by
    have h := LinearMap.congr_fun hg (Finsupp.single j 1)
    simpa only [LinearMap.comp_apply, f, Finsupp.linearCombination_single, one_smul,
      LinearMap.id_apply] using h
  let P : Matrix ι ι (Polynomial k) := fun i j =>
    Polynomial.C (g (u j) i) + Polynomial.X * Polynomial.C (g (v j) i)
  have hzero : P.map (Polynomial.evalRingHom 0) = 1 := by
    ext i j
    change Polynomial.eval 0 (P i j) = if i = j then 1 else 0
    simp only [P, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X, zero_mul, add_zero, hgu, Finsupp.single_apply]
    by_cases h : i = j <;> simp [h, eq_comm]
  have hdet : P.det ≠ 0 := by
    intro h
    have he := (Polynomial.evalRingHom (0 : k)).map_det P
    change Polynomial.eval 0 P.det = (P.map (Polynomial.evalRingHom 0)).det at he
    rw [h, Polynomial.eval_zero, hzero, Matrix.det_one] at he
    exact zero_ne_one he
  obtain ⟨t, ht, hprod⟩ := exists_nonzero_eval (P.det * p) (mul_ne_zero hdet hp)
  have hsplit : P.det.eval t ≠ 0 ∧ p.eval t ≠ 0 :=
    mul_ne_zero_iff.mp (by simpa only [Polynomial.eval_mul] using hprod)
  have hpt := hsplit.1
  let q : V →ₗ[k] (ι → k) :=
    { toFun := fun a i => g a i
      map_add' := by intro a b; funext i; simp
      map_smul' := by intro c a; funext i; simp }
  have he : P.map (Polynomial.evalRingHom t) =
      Matrix.of (fun i j => q (u j + t • v j) i) := by
    ext i j
    change Polynomial.eval t (P i j) = g (u j + t • v j) i
    simp only [P, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X, map_add, map_smul, Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul]
  have hmatrix : (Matrix.of (fun i j => q (u j + t • v j) i)).det ≠ 0 := by
    rw [← he]
    have hd := (Polynomial.evalRingHom t).map_det P
    change Polynomial.eval t P.det = (P.map (Polynomial.evalRingHom t)).det at hd
    rw [← hd]
    exact hpt
  have hlin := Matrix.linearIndependent_cols_of_det_ne_zero hmatrix
  exact ⟨t, ht, hsplit.2, LinearIndependent.of_comp q hlin⟩

/-- Independence persists at a nonzero point, with no additional avoidance condition. -/
theorem generic_independent_line (u v : ι → V) (hu : LinearIndependent k u) :
    ∃ t : k, t ≠ 0 ∧ LinearIndependent k (fun i => u i + t • v i) := by
  obtain ⟨t, ht, _, hlin⟩ := generic_independent_line_avoiding u v hu 1 one_ne_zero
  exact ⟨t, ht, hlin⟩

end NSP14.Green
