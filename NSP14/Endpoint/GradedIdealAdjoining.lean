module
public import NSP14.Endpoint.ArtinShift
public import NSP14.Homological.IdealAdjoiningKoszul
public import NSP14.Homological.GradedKoszulExact
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory HomologicalComplex NSP14.Homological
attribute [local instance] MvPolynomial.gradedAlgebra
namespace NSP14.Endpoint
variable (k σ : Type) [Field k] [Fintype σ] [LinearOrder σ]

/-- An actual homogeneous adjoining step, with the quotient's internal
degree shift proved through the same actual colon sequence. -/
theorem artin_adjoin_gradedBetti (J : Ideal (MvPolynomial σ k))
    (g h : MvPolynomial σ k) (x : σ)
    (hJ : J.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k))
    (hK : (J ⊔ Ideal.span {g}).IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k))
    (hC : (J.colon {g}).IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k))
    (n : ℕ) (hdeg : g.IsHomogeneous n) (he : g=MvPolynomial.X x*h)
    (hc : J.colon {g} ≤ J.colon {h}) (i : ℕ) (t : ℤ) :
    gradedBetti k σ (artinModule k σ (J ⊔ Ideal.span {g}))
        (artinGrading k σ (J ⊔ Ideal.span {g}) hK) (i+1) t=
      gradedBetti k σ (artinModule k σ J) (artinGrading k σ J hJ) (i+1) t+
      gradedBetti k σ (artinModule k σ (J.colon {g}))
        (artinGrading k σ (J.colon {g}) hC) i (t-(n:ℤ)) := by
  let R := MvPolynomial σ k
  let S := idealAdjoinSequence R J g
  let G1 := artinShiftedGrading k σ (J.colon {g}) hC (n:ℤ)
  let G2 := artinGrading k σ J hJ
  let G3 := artinGrading k σ (J ⊔ Ideal.span {g}) hK
  have hfm : ∀ a : S.X₁,artinMultiplyMap k σ (J.colon {g}) J g le_rfl a=S.f a := by
    intro a
    obtain ⟨b,rfl⟩ := Submodule.mkQ_surjective (J.colon {g}) a
    rfl
  have hf : ∀ q (a : coefficientModule k σ S.X₁),a ∈ G1.degreeSpace q → S.f a ∈ G2.degreeSpace q := by
    intro q a ha
    change a ∈ (artinShiftedGrading k σ (J.colon {g}) hC (n:ℤ)).degreeSpace q at ha
    rw [artinShifted_degreeSpace] at ha
    have hm := artinMultiplyMap_homogeneous k σ (J.colon {g}) J hC hJ g le_rfl n hdeg (q-(n:ℤ)) a ha
    have hm' : artinMultiplyMap k σ (J.colon {g}) J g le_rfl a ∈ G2.degreeSpace q := by
      simpa only [sub_add_cancel] using hm
    exact (hfm a) ▸ hm'
  have hg : ∀ q (a : coefficientModule k σ S.X₂),a ∈ G2.degreeSpace q → S.g a ∈ G3.degreeSpace q := by
    intro q a ha
    exact artinQuotientMap_homogeneous k σ J (J ⊔ Ideal.span {g}) hJ hK le_sup_left q a ha
  have hz : ∀ j,homologyMap ((coefficientKoszulFunctor k σ).map S.f) j=0 := by
    intro j
    change homologyMap ((coefficientKoszulFunctor k σ).map (idealAdjoinLeft R J g)) j=0
    rw [idealAdjoinLeft_factor R J g (MvPolynomial.X x) h he hc]
    exact coefficientKoszul_variable_smul_zero k σ _ x j
  let : Module.Finite (VariableRing k σ) S.X₁ := by
    change Module.Finite (VariableRing k σ) (R ⧸ J.colon {g})
    infer_instance
  let : Module.Finite (VariableRing k σ) S.X₂ := by
    change Module.Finite (VariableRing k σ) (R ⧸ J)
    infer_instance
  let : Module.Finite (VariableRing k σ) S.X₃ := by
    change Module.Finite (VariableRing k σ) (R ⧸ (J ⊔ Ideal.span {g}))
    infer_instance
  have hb := graded_quotient_betti_additivity k σ S G1 G2 G3 hf hg
    (idealAdjoinSequence_shortExact R J g) hz i t
  change gradedBetti k σ (artinModule k σ (J ⊔ Ideal.span {g}))
        (artinGrading k σ (J ⊔ Ideal.span {g}) hK) (i+1) t=
      gradedBetti k σ (artinModule k σ J) (artinGrading k σ J hJ) (i+1) t+
      gradedBetti k σ (artinModule k σ (J.colon {g}))
        (artinShiftedGrading k σ (J.colon {g}) hC (n:ℤ)) i t at hb
  rw [artinShifted_gradedBetti] at hb
  exact hb

end NSP14.Endpoint
