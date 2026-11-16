module
public import NSP14.Endpoint.StandardArtinGrading
public import NSP14.Homological.KoszulGradedMaps
public import Mathlib.RingTheory.Ideal.Colon
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open scoped Classical
open CategoryTheory NSP14.Homological
attribute [local instance] MvPolynomial.gradedAlgebra

namespace NSP14.Homological
variable (k σ A B : Type) [Field k]
  (M N : ModuleCat (VariableRing k σ))
  (c : coefficientModule k σ M ≃ₗ[k] (A →₀ k))
  (d : coefficientModule k σ N ≃ₗ[k] (B →₀ k))
  (degA : A → ℤ) (degB : B → ℤ)

theorem coordinateMap_degree (f : M ⟶ N) (s : ℤ)
    (hb : ∀ p j,degB j ≠ degA p+s → d (f (c.symm (Finsupp.single p 1))) j=0)
    (q : ℤ) (a : coefficientModule k σ M)
    (ha : a ∈ (coordinateDegreeInclusion k A degA σ M c q).range) :
    f a ∈ (coordinateDegreeInclusion k B degB σ N d (q+s)).range := by
  let L : (A →₀ k) →ₗ[k] (B →₀ k) := d.toLinearMap.comp ((coefficientMap k σ f).comp c.symm.toLinearMap)
  have hmap : Finsupp.supported k k {p | degA p=q} ≤
      (Finsupp.supported k k {j | degB j=q+s}).comap L := by
    rw [Finsupp.supported_eq_span_single]
    apply Submodule.span_le.mpr
    rintro _ ⟨p,hp,rfl⟩
    change L (Finsupp.single p 1) ∈ Finsupp.supported k k {j | degB j=q+s}
    rw [Finsupp.mem_supported']
    intro j hj
    exact hb p j (by change degA p=q at hp; rw [hp]; exact hj)
  have hin : c a ∈ Finsupp.supported k k {p | degA p=q} := by
    rw [Finsupp.mem_supported']
    exact (coordinateDegreeInclusion_range k A degA σ M c q a).mp ha
  have hout := hmap hin
  change L (c a) ∈ Finsupp.supported k k {j | degB j=q+s} at hout
  rw [Finsupp.mem_supported'] at hout
  rw [coordinateDegreeInclusion_range]
  intro j hj
  have h := hout j hj
  change d (f (c.symm (c a))) j=0 at h
  simpa only [LinearEquiv.symm_apply_apply] using h
end NSP14.Homological

namespace NSP14.Endpoint
variable (k σ : Type) [Field k] [Fintype σ] [LinearOrder σ]

/-- The image of every actual homogeneous polynomial lies in the same
degree of the actual standard-monomial quotient grading. -/
theorem artin_mk_homogeneous (I : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k))
    (n : ℕ) (f : MvPolynomial σ k) (hf : f.IsHomogeneous n) :
    (show coefficientModule k σ (artinModule k σ I) from Ideal.Quotient.mk I f) ∈
      (artinGrading k σ I hI).degreeSpace (n:ℤ) := by
  change _ ∈ (coordinateDegreeInclusion k (StandardExponent MonomialOrder.degLex I)
    (fun p => (p.val.degree:ℤ)) σ (artinModule k σ I) (artinCoordinates k σ I) (n:ℤ)).range
  rw [coordinateDegreeInclusion_range]
  intro j hj
  let r := (standardMonomialQuotientEquiv MonomialOrder.degLex I).symm (Ideal.Quotient.mk I f)
  have hr := normal_homogeneous k σ I hI n f hf r (normal_quotient_difference k σ I f)
  change r.val.coeff j.val=0
  by_contra hc
  have hd : j.val.degree=n := by
    rw [MvPolynomial.IsHomogeneous,MvPolynomial.IsWeightedHomogeneous] at hr
    exact (DFunLike.congr_fun Finsupp.degree_eq_weight_one j.val).trans (hr hc)
  exact hj (by exact_mod_cast hd)

theorem artinMap_homogeneous_of_basis
    (I J : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k))
    (hJ : J.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k))
    (f : artinModule k σ I ⟶ artinModule k σ J) (s : ℤ)
    (hb : ∀ p : StandardExponent MonomialOrder.degLex I,
      f ((artinCoordinates k σ I).symm (Finsupp.single p 1)) ∈
        (artinGrading k σ J hJ).degreeSpace ((p.val.degree:ℤ)+s))
    (q : ℤ) (a : coefficientModule k σ (artinModule k σ I))
    (ha : a ∈ (artinGrading k σ I hI).degreeSpace q) :
    f a ∈ (artinGrading k σ J hJ).degreeSpace (q+s) := by
  apply coordinateMap_degree k σ (StandardExponent MonomialOrder.degLex I)
    (StandardExponent MonomialOrder.degLex J) (artinModule k σ I) (artinModule k σ J)
    (artinCoordinates k σ I) (artinCoordinates k σ J)
    (fun p => (p.val.degree:ℤ)) (fun p => (p.val.degree:ℤ)) f s ?_ q a ha
  intro p j hj
  exact (coordinateDegreeInclusion_range k (StandardExponent MonomialOrder.degLex J)
    (fun p => (p.val.degree:ℤ)) σ (artinModule k σ J) (artinCoordinates k σ J)
    ((p.val.degree:ℤ)+s) _).mp (hb p) j hj

noncomputable def artinQuotientMap (I J : Ideal (MvPolynomial σ k)) (hIJ : I ≤ J) :
    artinModule k σ I ⟶ artinModule k σ J :=
  ModuleCat.ofHom (I.mapQ J LinearMap.id (by intro a ha; exact hIJ ha))

omit [Fintype σ] [LinearOrder σ] in
theorem artinQuotientMap_mk (I J : Ideal (MvPolynomial σ k)) (hIJ : I ≤ J) (f : MvPolynomial σ k) :
    artinQuotientMap k σ I J hIJ (Ideal.Quotient.mk I f)=Ideal.Quotient.mk J f := rfl

theorem artinQuotientMap_homogeneous (I J : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k))
    (hJ : J.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k)) (hIJ : I ≤ J)
    (q : ℤ) (a : coefficientModule k σ (artinModule k σ I))
    (ha : a ∈ (artinGrading k σ I hI).degreeSpace q) :
    artinQuotientMap k σ I J hIJ a ∈ (artinGrading k σ J hJ).degreeSpace q := by
  have hb : ∀ p : StandardExponent MonomialOrder.degLex I,
      artinQuotientMap k σ I J hIJ ((artinCoordinates k σ I).symm (Finsupp.single p 1)) ∈
        (artinGrading k σ J hJ).degreeSpace ((p.val.degree:ℤ)+0) := by
    intro p
    rw [artinCoordinates_single,artinQuotientMap_mk]
    simpa only [add_zero] using artin_mk_homogeneous k σ J hJ p.val.degree
      (MvPolynomial.monomial p.val (1:k)) (MvPolynomial.isHomogeneous_monomial (1:k) rfl)
  simpa only [add_zero] using artinMap_homogeneous_of_basis k σ I J hI hJ
    (artinQuotientMap k σ I J hIJ) 0 hb q a ha

noncomputable def artinMultiplyMap (I J : Ideal (MvPolynomial σ k)) (g : MvPolynomial σ k)
    (hIJ : I ≤ J.colon {g}) : artinModule k σ I ⟶ artinModule k σ J :=
  ModuleCat.ofHom (I.mapQ J (LinearMap.mulLeft (MvPolynomial σ k) g) (by
    intro a ha
    change g*a ∈ J
    simpa only [smul_eq_mul,mul_comm] using Submodule.mem_colon_singleton.mp (hIJ ha)))

omit [Fintype σ] [LinearOrder σ] in
theorem artinMultiplyMap_mk (I J : Ideal (MvPolynomial σ k)) (g : MvPolynomial σ k)
    (hIJ : I ≤ J.colon {g}) (f : MvPolynomial σ k) :
    artinMultiplyMap k σ I J g hIJ (Ideal.Quotient.mk I f)=Ideal.Quotient.mk J (g*f) := rfl

theorem artinMultiplyMap_homogeneous (I J : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k))
    (hJ : J.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k))
    (g : MvPolynomial σ k) (hIJ : I ≤ J.colon {g}) (n : ℕ) (hg : g.IsHomogeneous n)
    (q : ℤ) (a : coefficientModule k σ (artinModule k σ I))
    (ha : a ∈ (artinGrading k σ I hI).degreeSpace q) :
    artinMultiplyMap k σ I J g hIJ a ∈ (artinGrading k σ J hJ).degreeSpace (q+(n:ℤ)) := by
  apply artinMap_homogeneous_of_basis k σ I J hI hJ (artinMultiplyMap k σ I J g hIJ) (n:ℤ) ?_ q a ha
  intro p
  rw [artinCoordinates_single,artinMultiplyMap_mk]
  have hh := artin_mk_homogeneous k σ J hJ (n+p.val.degree)
    (g*MvPolynomial.monomial p.val (1:k)) (hg.mul (MvPolynomial.isHomogeneous_monomial (1:k) rfl))
  have he : ((n+p.val.degree:ℕ):ℤ)=(p.val.degree:ℤ)+(n:ℤ) := by push_cast; omega
  rw [he] at hh
  exact hh

theorem artinGradedBetti_congr (I J : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k))
    (hJ : J.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k))
    (he : I=J) (i : ℕ) (t : ℤ) :
    gradedBetti k σ (artinModule k σ I) (artinGrading k σ I hI) i t=
      gradedBetti k σ (artinModule k σ J) (artinGrading k σ J hJ) i t := by
  subst J
  rfl

end NSP14.Endpoint
