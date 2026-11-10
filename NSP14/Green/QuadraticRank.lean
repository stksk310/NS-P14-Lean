module

public import NSP14.Green.RankChoice
public import NSP14.Green.BilinearQuotient

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open scoped Classical

namespace NSP14.Green

variable {k V W : Type*} [Field k] [Infinite k]
  [AddCommGroup V] [Module k V] [Module.Finite k V]
  [AddCommGroup W] [Module k W] [Module.Finite k W]

/-- The degree-two rank theorem behind the required Green special case.
The alternating case is retained explicitly, so characteristic two is covered. -/
theorem quadratic_rank_bound_at (μ : V →ₗ[k] V →ₗ[k] W)
    (hs : ∀ x y, μ x y = μ y x) (hspan : bilinearSpan μ = ⊤)
    (x : V) (hmax : ∀ y : V, Module.finrank k (μ y).range ≤ Module.finrank k (μ x).range)
    (hcase : (∀ y : V, μ y y = 0) ∨ μ x x ≠ 0) :
    Module.finrank k W ≤ (Module.finrank k (μ x).range + 1).choose 2 := by
  let F := μ x
  let U := F.range
  have hkernel : ∀ z ∈ F.ker, ∀ y : V, μ z y ∈ U := by
    intro z hz y
    rw [hs z y]
    apply maximal_rank_kernel F (μ y) ?_ z hz
    intro t
    have he : μ (x + t • y) = μ x + t • μ y := by rw [map_add, map_smul]
    change Module.finrank k (μ x + t • μ y).range ≤ Module.finrank k (μ x).range
    rw [← he]
    exact hmax (x + t • y)
  have hsum := U.finrank_quotient_add_finrank
  have hchoose : (Module.finrank k U + 1).choose 2 =
      Module.finrank k U + (Module.finrank k U).choose 2 := by
    rw [Nat.choose_succ_succ', Nat.choose_one_right]
  rcases hcase with halt | hx
  · let Q := quotientBilinear μ F.ker U hkernel hs
    have hsym : ∀ a b, Q a b = Q b a := quotientBilinear_symmetric μ F.ker U hkernel hs
    have hsp : bilinearSpan Q = ⊤ := quotientBilinear_spans μ F.ker U hkernel hs hspan
    have hal : ∀ a : V ⧸ F.ker, Q a a = 0 := by
      intro a
      refine Submodule.Quotient.induction_on F.ker a ?_
      intro y
      change U.mkQ (μ y y) = 0
      rw [halt, map_zero]
    have hbound := alternating_span_bound Q hsym hal hsp
    have hdim : Module.finrank k (V ⧸ F.ker) = Module.finrank k U := F.quotKerEquivRange.finrank_eq
    rw [hdim] at hbound
    change Module.finrank k W ≤ (Module.finrank k U + 1).choose 2
    rw [hchoose]
    omega
  · let H := F.ker ⊔ Submodule.span k {x}
    have hleft : ∀ z ∈ H, ∀ y : V, μ z y ∈ U := by
      intro z hz y
      obtain ⟨a,ha,b,hb,he⟩ := Submodule.mem_sup.mp hz
      obtain ⟨c,rfl⟩ := Submodule.mem_span_singleton.mp hb
      rw [← he, map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply]
      exact U.add_mem (hkernel a ha y) (U.smul_mem c ⟨y,rfl⟩)
    let Q := quotientBilinear μ H U hleft hs
    have hsym : ∀ a b, Q a b = Q b a := quotientBilinear_symmetric μ H U hleft hs
    have hsp : bilinearSpan Q = ⊤ := quotientBilinear_spans μ H U hleft hs hspan
    have hx0 : x ≠ 0 := by intro h; apply hx; simp [h]
    have hd : Disjoint F.ker (Submodule.span k {x}) :=
      Submodule.disjoint_span_singleton.mpr (fun h => (hx h).elim)
    have hsup := F.ker.finrank_sup_add_finrank_inf_eq (Submodule.span k {x})
    rw [hd.eq_bot, finrank_bot, add_zero, finrank_span_singleton hx0] at hsup
    have hquot := H.finrank_quotient_add_finrank
    have hrank : Module.finrank k U + Module.finrank k F.ker = Module.finrank k V :=
      F.finrank_range_add_finrank_ker
    have hdim : Module.finrank k (V ⧸ H) + 1 = Module.finrank k U := by
      change Module.finrank k H = _ at hsup
      omega
    have hbound := symmetric_span_bound Q hsym hsp
    rw [hdim] at hbound
    change Module.finrank k W ≤ (Module.finrank k U + 1).choose 2
    rw [hchoose]
    omega

/-- Maximum multiplication rank always satisfies the triangular image bound. -/
theorem exists_quadratic_rank_bound (μ : V →ₗ[k] V →ₗ[k] W)
    (hs : ∀ x y, μ x y = μ y x) (hspan : bilinearSpan μ = ⊤) :
    ∃ x : V, Module.finrank k W ≤ (Module.finrank k (μ x).range + 1).choose 2 := by
  by_cases ha : ∀ y : V, μ y y = 0
  · obtain ⟨x,hmax⟩ := exists_maximal_rank (fun x => μ x)
    exact ⟨x, quadratic_rank_bound_at μ hs hspan x hmax (Or.inl ha)⟩
  · push Not at ha
    obtain ⟨x,hx,hmax⟩ := exists_maximal_rank_nonisotropic μ ha
    exact ⟨x, quadratic_rank_bound_at μ hs hspan x hmax (Or.inr hx)⟩

end NSP14.Green
