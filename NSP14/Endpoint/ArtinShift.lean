module
public import NSP14.Endpoint.ArtinGradedMaps
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open scoped Classical
open CategoryTheory HomologicalComplex NSP14.Homological
attribute [local instance] MvPolynomial.gradedAlgebra
namespace NSP14.Endpoint
variable (k σ : Type) [Field k] [Fintype σ] [LinearOrder σ]

/-- A shifted grading on the very same quotient module and actual
standard monomial basis. No new polynomial-module action is introduced. -/
noncomputable def artinShiftedGrading (I : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k)) (s : ℤ) :
    GradedPolynomialModule k σ (artinModule k σ I) :=
  basisGrading k σ (StandardExponent MonomialOrder.degLex I) (artinModule k σ I)
    (artinCoordinates k σ I) (fun p => (p.val.degree:ℤ)+s) (by
      intro x p j hj
      apply artin_variable_homogeneous k σ I hI x p j
      intro he
      apply hj
      omega)

theorem artinShifted_degreeSpace (I : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k)) (s q : ℤ) :
    (artinShiftedGrading k σ I hI s).degreeSpace q=
      (artinGrading k σ I hI).degreeSpace (q-s) := by
  ext a
  change a ∈ (coordinateDegreeInclusion k (StandardExponent MonomialOrder.degLex I)
      (fun p => (p.val.degree:ℤ)+s) σ (artinModule k σ I) (artinCoordinates k σ I) q).range ↔
    a ∈ (coordinateDegreeInclusion k (StandardExponent MonomialOrder.degLex I)
      (fun p => (p.val.degree:ℤ)) σ (artinModule k σ I) (artinCoordinates k σ I) (q-s)).range
  rw [coordinateDegreeInclusion_range,coordinateDegreeInclusion_range]
  constructor
  · intro h p hp
    apply h p
    omega
  · intro h p hp
    apply h p
    omega

/-- Internal degrees shift on actual graded Koszul homology through
the actual identity polynomial-module isomorphism. -/
theorem artinShifted_gradedBetti (I : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k)) (s : ℤ) (i : ℕ) (t : ℤ) :
    gradedBetti k σ (artinModule k σ I) (artinShiftedGrading k σ I hI s) i t=
      gradedBetti k σ (artinModule k σ I) (artinGrading k σ I hI) i (t-s) := by
  let G := artinShiftedGrading k σ I hI s
  let H := artinGrading k σ I hI
  have hf : ∀ q (a : coefficientModule k σ (artinModule k σ I)),
      (Iso.refl (artinModule k σ I)).hom a ∈ H.degreeSpace (q+(-s)) ↔ a ∈ G.degreeSpace q := by
    intro q a
    change a ∈ (artinGrading k σ I hI).degreeSpace (q+(-s)) ↔
      a ∈ (artinShiftedGrading k σ I hI s).degreeSpace q
    rw [artinShifted_degreeSpace]
    simp only [sub_eq_add_neg]
  let e := gradedKoszulIso k σ G H (Iso.refl (artinModule k σ I)) (-s) hf (variableList k σ) t
  have h := ((homologyFunctor _ (ComplexShape.down ℕ) i).mapIso e).toLinearEquiv.finrank_eq
  change gradedBetti k σ (artinModule k σ I) G i t=
    gradedBetti k σ (artinModule k σ I) H i (t+(-s)) at h
  simpa only [sub_eq_add_neg] using h

end NSP14.Endpoint
