module

public import NSP14.Green.BilinearSpan
public import Mathlib.LinearAlgebra.Quotient.Basic

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open scoped Classical

namespace NSP14.Green

variable {k V W : Type*} [Field k] [AddCommGroup V] [Module k V]
  [AddCommGroup W] [Module k W]

noncomputable def bilinearSecond (μ : V →ₗ[k] V →ₗ[k] W)
    (H : Submodule k V) (U : Submodule k W)
    (hleft : ∀ x ∈ H, ∀ y, μ x y ∈ U) (hs : ∀ x y, μ x y = μ y x) :
    V →ₗ[k] (V ⧸ H) →ₗ[k] (W ⧸ U) where
  toFun x := H.mapQ U (μ x) (by
    intro y hy
    change μ x y ∈ U
    rw [hs]
    exact hleft y hy x)
  map_add' x y := by
    apply LinearMap.ext
    intro q
    refine Submodule.Quotient.induction_on H q ?_
    intro z
    change U.mkQ (μ (x + y) z) = U.mkQ (μ x z) + U.mkQ (μ y z)
    simp
  map_smul' c x := by
    apply LinearMap.ext
    intro q
    refine Submodule.Quotient.induction_on H q ?_
    intro z
    change U.mkQ (μ (c • x) z) = c • U.mkQ (μ x z)
    simp

noncomputable def quotientBilinear (μ : V →ₗ[k] V →ₗ[k] W)
    (H : Submodule k V) (U : Submodule k W)
    (hleft : ∀ x ∈ H, ∀ y, μ x y ∈ U) (hs : ∀ x y, μ x y = μ y x) :
    (V ⧸ H) →ₗ[k] (V ⧸ H) →ₗ[k] (W ⧸ U) :=
  H.liftQ (bilinearSecond μ H U hleft hs) (by
    intro x hx
    change bilinearSecond μ H U hleft hs x = 0
    apply LinearMap.ext
    intro q
    refine Submodule.Quotient.induction_on H q ?_
    intro y
    change (Submodule.Quotient.mk (μ x y) : W ⧸ U) = 0
    rw [Submodule.Quotient.mk_eq_zero]
    exact hleft x hx y)

@[simp] theorem quotientBilinear_mk (μ : V →ₗ[k] V →ₗ[k] W)
    (H : Submodule k V) (U : Submodule k W)
    (hleft : ∀ x ∈ H, ∀ y, μ x y ∈ U) (hs : ∀ x y, μ x y = μ y x) (x y : V) :
    quotientBilinear μ H U hleft hs (H.mkQ x) (H.mkQ y) = U.mkQ (μ x y) := rfl

theorem quotientBilinear_symmetric (μ : V →ₗ[k] V →ₗ[k] W)
    (H : Submodule k V) (U : Submodule k W)
    (hleft : ∀ x ∈ H, ∀ y, μ x y ∈ U) (hs : ∀ x y, μ x y = μ y x)
    (x y : V ⧸ H) :
    quotientBilinear μ H U hleft hs x y = quotientBilinear μ H U hleft hs y x := by
  refine Submodule.Quotient.induction_on H x ?_
  intro a
  refine Submodule.Quotient.induction_on H y ?_
  intro b
  simp only [← Submodule.mkQ_apply, quotientBilinear_mk, hs a b]

theorem quotientBilinear_spans (μ : V →ₗ[k] V →ₗ[k] W)
    (H : Submodule k V) (U : Submodule k W)
    (hleft : ∀ x ∈ H, ∀ y, μ x y ∈ U) (hs : ∀ x y, μ x y = μ y x)
    (hspan : bilinearSpan μ = ⊤) :
    bilinearSpan (quotientBilinear μ H U hleft hs) = ⊤ := by
  have hle : (bilinearSpan μ).map U.mkQ ≤ bilinearSpan (quotientBilinear μ H U hleft hs) := by
    rw [bilinearSpan, Submodule.map_span]
    apply Submodule.span_le.mpr
    rintro z ⟨w, ⟨a,b,rfl⟩, rfl⟩
    exact Submodule.subset_span ⟨H.mkQ a,H.mkQ b,rfl⟩
  rw [hspan, Submodule.map_top, Submodule.range_mkQ] at hle
  exact top_unique hle

end NSP14.Green
