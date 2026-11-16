module

public import NSP14.Green.QuadraticRank

@[expose] public section

open scoped Classical

namespace NSP14.Green

/-- Integer accounting for the degree-two Green decrement. -/
theorem green_decrement_arithmetic {a q R p b : ℕ}
    (hcap : a ≤ (p + 1).choose 2 + b) (hrank : a ≤ (R + 1).choose 2)
    (hq : q + R = a) : q ≤ p.choose 2 + (b - 1) := by
  have hR : (R + 1).choose 2 = R + R.choose 2 := by
    rw [Nat.choose_succ_succ', Nat.choose_one_right]
  have hp : (p + 1).choose 2 = p + p.choose 2 := by
    rw [Nat.choose_succ_succ', Nat.choose_one_right]
  rw [hR] at hrank
  rw [hp] at hcap
  by_cases hle : R ≤ p
  · have hc := Nat.choose_le_choose 2 hle
    omega
  · omega

variable {k V W : Type*} [Field k] [Infinite k]
  [AddCommGroup V] [Module k V] [Module.Finite k V]
  [AddCommGroup W] [Module k W] [Module.Finite k W]

/-- A nonzero hyperplane vector satisfying the required degree-two decrement.
This is an existence theorem, not an input hypothesis about a generic cut. -/
theorem exists_hyperplane_step (μ : V →ₗ[k] V →ₗ[k] W)
    (hs : ∀ x y, μ x y = μ y x) (hspan : bilinearSpan μ = ⊤)
    (p b : ℕ) (hp : 1 ≤ p) (hdim : p ≤ Module.finrank k V)
    (hcap : Module.finrank k W ≤ (p + 1).choose 2 + b) :
    ∃ x : V, x ≠ 0 ∧ Module.finrank k (W ⧸ (μ x).range) ≤ p.choose 2 + (b - 1) := by
  have : Nontrivial V := Module.nontrivial_of_finrank_pos (R := k) (by omega)
  by_cases hzero : Module.finrank k W = 0
  · obtain ⟨x,hx⟩ := exists_ne (0 : V)
    refine ⟨x,hx,?_⟩
    have hq := (μ x).range.finrank_quotient_add_finrank
    omega
  · obtain ⟨x,hrank⟩ := exists_quadratic_rank_bound μ hs hspan
    have hx : x ≠ 0 := by
      intro he
      have hf : μ x = 0 := by rw [he, map_zero]
      have hr : Module.finrank k (μ x).range = 0 := by
        rw [hf, LinearMap.range_zero]
        exact finrank_bot k W
      rw [hr] at hrank
      norm_num at hrank
      omega
    refine ⟨x,hx,?_⟩
    exact green_decrement_arithmetic hcap hrank ((μ x).range.finrank_quotient_add_finrank)

/-- The product descends after one cut in both degree one and degree two. -/
noncomputable def hyperplaneProduct (μ : V →ₗ[k] V →ₗ[k] W)
    (hs : ∀ x y, μ x y = μ y x) (x : V) :
    (V ⧸ Submodule.span k {x}) →ₗ[k]
      (V ⧸ Submodule.span k {x}) →ₗ[k] (W ⧸ (μ x).range) :=
  quotientBilinear μ (Submodule.span k {x}) (μ x).range (by
    intro z hz y
    obtain ⟨c,rfl⟩ := Submodule.mem_span_singleton.mp hz
    rw [map_smul, LinearMap.smul_apply]
    exact (μ x).range.smul_mem c ⟨y,rfl⟩) hs

omit [Infinite k] [Module.Finite k V] [Module.Finite k W] in
@[simp] theorem hyperplaneProduct_mk (μ : V →ₗ[k] V →ₗ[k] W)
    (hs : ∀ x y, μ x y = μ y x) (x a b : V) :
    hyperplaneProduct μ hs x (Submodule.Quotient.mk a) (Submodule.Quotient.mk b) =
      (Submodule.Quotient.mk (μ a b) : W ⧸ (μ x).range) := rfl

omit [Infinite k] [Module.Finite k V] [Module.Finite k W] in
theorem hyperplaneProduct_symmetric (μ : V →ₗ[k] V →ₗ[k] W)
    (hs : ∀ x y, μ x y = μ y x) (x : V) :
    ∀ a b, hyperplaneProduct μ hs x a b = hyperplaneProduct μ hs x b a :=
  quotientBilinear_symmetric μ _ _ _ hs

omit [Infinite k] [Module.Finite k V] [Module.Finite k W] in
theorem hyperplaneProduct_spans (μ : V →ₗ[k] V →ₗ[k] W)
    (hs : ∀ x y, μ x y = μ y x) (hspan : bilinearSpan μ = ⊤) (x : V) :
    bilinearSpan (hyperplaneProduct μ hs x) = ⊤ :=
  quotientBilinear_spans μ _ _ _ hs hspan

end NSP14.Green
