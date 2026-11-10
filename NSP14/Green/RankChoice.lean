module

public import NSP14.Green.MaximalRank
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Tactic.Ring

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open scoped Classical

namespace NSP14.Green

variable {k V W : Type*} [Field k] [Infinite k]
  [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W] [Module.Finite k W]

omit [Infinite k] in
theorem exists_maximal_rank (F : V → (V →ₗ[k] W)) :
    ∃ x : V, ∀ y : V, Module.finrank k (F y).range ≤ Module.finrank k (F x).range := by
  have hb (y : V) : Module.finrank k (F y).range ≤ Module.finrank k W :=
    Submodule.finrank_le _
  let r := Nat.findGreatest (fun n => ∃ x : V, Module.finrank k (F x).range = n) (Module.finrank k W)
  have hr : ∃ x : V, Module.finrank k (F x).range = r :=
    Nat.findGreatest_spec (P := fun n => ∃ x : V, Module.finrank k (F x).range = n)
      (hb 0) ⟨0,rfl⟩
  obtain ⟨x,hx⟩ := hr
  refine ⟨x, ?_⟩
  intro y
  rw [hx]
  exact Nat.le_findGreatest (hb y) ⟨y,rfl⟩

/-- If squares do not all vanish, maximum multiplication rank can be attained
at a vector whose square is nonzero. The polynomial argument uses no 2⁻¹. -/
theorem exists_maximal_rank_nonisotropic (μ : V →ₗ[k] V →ₗ[k] W)
    (ha : ∃ y : V, μ y y ≠ 0) :
    ∃ x : V, μ x x ≠ 0 ∧
      ∀ y : V, Module.finrank k (μ y).range ≤ Module.finrank k (μ x).range := by
  obtain ⟨x,hmax⟩ := exists_maximal_rank (fun x => μ x)
  obtain ⟨y,hy⟩ := ha
  obtain ⟨(ℓ : W →ₗ[k] k),hℓ⟩ := Module.Projective.exists_dual_eq_one k hy
  let B := Module.finBasis k (μ x).range
  let u : Fin (Module.finrank k (μ x).range) → V := fun i => (B i).property.choose
  have hu (i : Fin (Module.finrank k (μ x).range)) : μ x (u i) = (B i).val :=
    (B i).property.choose_spec
  have hind : LinearIndependent k (fun i => μ x (u i)) := by
    have hb := B.linearIndependent.map' (μ x).range.subtype (Submodule.ker_subtype _)
    change LinearIndependent k (fun i => (B i).val) at hb
    convert hb using 1
    funext i
    exact hu i
  let p : Polynomial k := Polynomial.C (ℓ (μ x x)) +
    Polynomial.X * Polynomial.C (ℓ (μ x y + μ y x)) + Polynomial.X ^ 2
  have hp : p ≠ 0 := by
    intro h
    have he := congrArg (fun q : Polynomial k => q.coeff 2) h
    norm_num [p] at he
  have hp_eval (t : k) : p.eval t = ℓ (μ (x + t • y) (x + t • y)) := by
    simp only [p, Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_mul, Polynomial.eval_X,
      Polynomial.eval_pow, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, hℓ, smul_eq_mul]
    ring
  obtain ⟨t, _, ht, hLI⟩ := generic_independent_line_avoiding
    (fun i => μ x (u i)) (fun i => μ y (u i)) hind p hp
  let z := x + t • y
  have hmem (i : Fin (Module.finrank k (μ x).range)) :
      μ x (u i) + t • μ y (u i) ∈ (μ z).range := by
    refine ⟨u i, ?_⟩
    simp [z]
  have hsub : LinearIndependent k (fun i =>
      (⟨μ x (u i) + t • μ y (u i), hmem i⟩ : (μ z).range)) :=
    LinearIndependent.of_comp (μ z).range.subtype hLI
  have hr : Module.finrank k (μ x).range ≤ Module.finrank k (μ z).range := by
    simpa only [Fintype.card_fin] using hsub.fintype_card_le_finrank
  refine ⟨z, ?_, fun w => (hmax w).trans hr⟩
  intro hz
  have he := hp_eval t
  rw [show x + t • y = z from rfl, hz, map_zero] at he
  exact ht he

end NSP14.Green
