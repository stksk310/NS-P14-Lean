module
public import NSP14.Endpoint.StandardArtinAugmentation
public import NSP14.Endpoint.FirstHarmonic
public import NSP14.Endpoint.ArtinRank
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open scoped Classical
open CategoryTheory NSP14.Homological
attribute [local instance] MvPolynomial.gradedAlgebra
namespace NSP14.Endpoint
variable (k σ : Type) [Field k] [Fintype σ] [LinearOrder σ]
  (I : Ideal (MvPolynomial σ k)) (hproper : I≠⊤)
  (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k))
  (hlinear : ∀ f∈I, f.IsHomogeneous 1 → f=0)

noncomputable def artinUnit : coefficientModule k σ (artinModule k σ I) := (coefficientOriginalEquiv k σ _).symm 1

theorem artinUnit_coordinates : artinCoordinates k σ I (artinUnit k σ I)=
    Finsupp.single (artinZeroIndex k σ I hproper hI hlinear) 1 := by
  apply (artinCoordinates k σ I).symm.injective
  rw [LinearEquiv.symm_apply_apply,artinCoordinates_single]
  change (1 : MvPolynomial σ k ⧸ I)=Ideal.Quotient.mk I (MvPolynomial.monomial 0 1)
  exact (map_one (Ideal.Quotient.mk I)).symm

include hproper hlinear in
theorem artinUnit_degree_zero : artinUnit k σ I∈(artinGrading k σ I hI).degreeSpace 0 := by
  change artinUnit k σ I∈(coordinateDegreeInclusion k (StandardExponent MonomialOrder.degLex I) (fun p => (p.val.degree : ℤ)) σ
    (artinModule k σ I) (artinCoordinates k σ I) 0).range
  rw [coordinateDegreeInclusion_range]
  intro p hp
  rw [artinUnit_coordinates k σ I hproper hI hlinear]
  apply Finsupp.single_eq_of_ne
  intro he
  subst p
  exact hp rfl

include hproper hlinear in
theorem artin_generated_zero : Submodule.span (VariableRing k σ)
    (Set.range (fun a : (artinGrading k σ I hI).piece 0 =>
      (show artinModule k σ I from (artinGrading k σ I hI).inclusion 0 a)))=⊤ := by
  let U := Submodule.span (VariableRing k σ)
    (Set.range (fun a : (artinGrading k σ I hI).piece 0 =>
      (show artinModule k σ I from (artinGrading k σ I hI).inclusion 0 a)))
  have hu : (show artinModule k σ I from artinUnit k σ I)∈U :=
    Submodule.subset_span (artinUnit_degree_zero k σ I hproper hI hlinear)
  apply top_unique
  intro a _
  obtain ⟨p,hp⟩ := Ideal.Quotient.mkₐ_surjective k I a
  have hm := U.smul_mem p hu
  have he : p • (show artinModule k σ I from artinUnit k σ I)=a := by
    change Ideal.Quotient.mk I p*1=a
    rw [mul_one]
    exact hp
  exact he ▸ hm

noncomputable def artinLinearFunctional (x : σ) : coefficientModule k σ (artinModule k σ I) →ₗ[k] k :=
  (Finsupp.lapply (artinLinearIndex k σ I hproper hI hlinear x)).comp (artinCoordinates k σ I).toLinearMap

theorem artin_linear_functionals (v w : σ) :
    artinLinearFunctional k σ I hproper hI hlinear v
      ((MvPolynomial.X w : VariableRing k σ) • artinUnit k σ I)=if v=w then 1 else 0 := by
  have he : (MvPolynomial.X w : VariableRing k σ) • artinUnit k σ I=
      (artinCoordinates k σ I).symm (Finsupp.single (artinLinearIndex k σ I hproper hI hlinear w) 1) := by
    rw [artinCoordinates_single]
    change Ideal.Quotient.mk I (MvPolynomial.X w)*1=Ideal.Quotient.mk I (MvPolynomial.monomial (Finsupp.single w 1) 1)
    rw [mul_one]
    rfl
  rw [he]
  change artinCoordinates k σ I ((artinCoordinates k σ I).symm _) _=_
  rw [LinearEquiv.apply_symm_apply,Finsupp.single_apply]
  have hi : artinLinearIndex k σ I hproper hI hlinear w=artinLinearIndex k σ I hproper hI hlinear v ↔ v=w := by
    constructor
    · intro h
      have hh : Finsupp.single w 1=Finsupp.single v 1 := congrArg Subtype.val h
      exact (Finsupp.single_left_injective (by decide : (1:ℕ)≠0) hh).symm
    · intro h
      subst w
      rfl
  simp only [hi]
end NSP14.Endpoint
