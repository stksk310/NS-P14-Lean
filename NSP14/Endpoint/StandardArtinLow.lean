module
public import NSP14.Endpoint.StandardArtinGrading
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open scoped Classical
open NSP14.Homological
attribute [local instance] MvPolynomial.gradedAlgebra
namespace NSP14.Endpoint
variable (k σ : Type) [Field k] [Fintype σ] [LinearOrder σ]
  (I : Ideal (MvPolynomial σ k)) (hproper : I≠⊤)
  (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k))
  (hlinear : ∀ f∈I, f.IsHomogeneous 1 → f=0)

omit [Fintype σ] [LinearOrder σ] in
include hproper hI in
/-- A proper homogeneous ideal contains no nonzero constant coefficient. -/
theorem homogeneous_ideal_constant (f : MvPolynomial σ k) (hf : f∈I) : f.coeff 0=0 := by
  have hc := MvPolynomial.homogeneousComponent_mem_of_mem hI hf 0
  rw [MvPolynomial.homogeneousComponent_zero] at hc
  by_contra hn
  have hu : IsUnit (MvPolynomial.C (f.coeff 0) : MvPolynomial σ k) := (isUnit_iff_ne_zero.mpr hn).map (MvPolynomial.C : k →+* MvPolynomial σ k)
  exact hproper (I.eq_top_of_isUnit_mem hc hu)

omit [Fintype σ] [LinearOrder σ] in
include hproper hI hlinear in
theorem homogeneous_ideal_low_coeff (f : MvPolynomial σ k) (hf : f∈I)
    (β : σ →₀ ℕ) (hβ : β.degree≤1) : f.coeff β=0 := by
  by_cases hz : β.degree=0
  · rw [(Finsupp.degree_eq_zero_iff β).mp hz]
    exact homogeneous_ideal_constant k σ I hproper hI f hf
  have he : β.degree=1 := by omega
  have hc := hlinear (MvPolynomial.homogeneousComponent 1 f)
    (MvPolynomial.homogeneousComponent_mem_of_mem hI hf 1)
    (MvPolynomial.homogeneousComponent_isHomogeneous 1 f)
  have := congrArg (fun p : MvPolynomial σ k => p.coeff β) hc
  simpa only [MvPolynomial.coeff_homogeneousComponent,he,ite_true,AddMonoidAlgebra.coeff_zero,Finsupp.zero_apply] using this

include hproper hI hlinear in
theorem low_exponent_standard (β : σ →₀ ℕ) (hβ : β.degree≤1) :
    β∈StandardExponent MonomialOrder.degLex I := by
  intro p hp hp0 hle
  have hd : (MonomialOrder.degLex.degree p).degree≤1 :=
    (Finsupp.degree_mono hle).trans hβ
  exact (MonomialOrder.degLex.coeff_degree_ne_zero_iff.mpr hp0)
    (homogeneous_ideal_low_coeff k σ I hproper hI hlinear p hp _ hd)

noncomputable def artinZeroIndex : StandardExponent MonomialOrder.degLex I :=
  ⟨0,low_exponent_standard k σ I hproper hI hlinear 0 (by simp)⟩

noncomputable def artinLinearIndex (x : σ) : StandardExponent MonomialOrder.degLex I :=
  ⟨Finsupp.single x 1,low_exponent_standard k σ I hproper hI hlinear _ (by simp)⟩

noncomputable def artinZeroEquiv :
    {p : StandardExponent MonomialOrder.degLex I // (p.val.degree : ℤ)=0} ≃ PUnit.{1} where
  toFun _ := PUnit.unit
  invFun _ := ⟨artinZeroIndex k σ I hproper hI hlinear,by simp [artinZeroIndex]⟩
  left_inv p := by
    apply Subtype.ext
    apply Subtype.ext
    have hn : p.val.val.degree=0 := by exact_mod_cast p.property
    exact (Finsupp.degree_eq_zero_iff p.val.val).mp hn |>.symm
  right_inv _ := rfl
end NSP14.Endpoint
namespace NSP14.Endpoint
open scoped Classical
open NSP14.Homological
attribute [local instance] MvPolynomial.gradedAlgebra
variable (k σ : Type) [Field k] [Fintype σ] [LinearOrder σ]
  (I : Ideal (MvPolynomial σ k)) (hproper : I≠⊤)
  (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k))
  (hlinear : ∀ f∈I, f.IsHomogeneous 1 → f=0)

noncomputable def artinOneEquiv : σ ≃
    {p : StandardExponent MonomialOrder.degLex I // (p.val.degree : ℤ)=1} :=
  Equiv.ofBijective (fun x => ⟨artinLinearIndex k σ I hproper hI hlinear x,by simp [artinLinearIndex]⟩)
    ⟨by
      intro x y h
      have he : Finsupp.single x 1=Finsupp.single y 1 := congrArg (fun p => p.val.val) h
      exact Finsupp.single_left_injective (by decide : (1:ℕ)≠0) he,by
      intro p
      have hd : p.val.val.degree=1 := by exact_mod_cast p.property
      have hr : p.val.val∈Set.range (fun x : σ => Finsupp.single x 1) := by
        rw [Finsupp.range_single_one]
        exact hd
      obtain ⟨x,hx⟩ := hr
      exact ⟨x,Subtype.ext (Subtype.ext hx)⟩⟩
end NSP14.Endpoint
