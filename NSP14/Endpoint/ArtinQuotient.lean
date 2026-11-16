module
public import NSP14.Endpoint.HomologyFinite
public import NSP14.Homological.ActionH0Image
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits HomologicalComplex NSP14.Homological
namespace NSP14.Endpoint
variable (k A : Type) [Field k] [CommRing A] [Algebra k A]

noncomputable def endpointIdeal (φ : MvPolynomial (Fin 2) k →ₐ[k] A) : Ideal A :=
  Ideal.span {a | a∈[φ (MvPolynomial.X 1),φ (MvPolynomial.X 0)]}

abbrev EndpointQuotient (φ : MvPolynomial (Fin 2) k →ₐ[k] A) := A ⧸ endpointIdeal k A φ

noncomputable def quotientCoefficientEquiv (I : Ideal A) :
    (ModuleCat.restrictScalars (algebraMap k A)).obj (ModuleCat.of A (A ⧸ I)) ≃ₗ[k] (A ⧸ I) where
  toFun a := a
  invFun a := a
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' c a := by
    change (algebraMap k A c) • (show A ⧸ I from a)=c • (show A ⧸ I from a)
    rw [algebraMap_smul]

noncomputable def endpointH0QuotientEquiv (φ : MvPolynomial (Fin 2) k →ₐ[k] A) :
    (regularPartialCoefficientComplex k A [φ (MvPolynomial.X 1),φ (MvPolynomial.X 0)]).homology 0 ≃ₗ[k]
      EndpointQuotient k A φ :=
  (nativeCoefficientHomologyIso k A (actionRegularComplex A [φ (MvPolynomial.X 1),φ (MvPolynomial.X 0)]) 0).toLinearEquiv.trans
    (((ModuleCat.restrictScalars (algebraMap k A)).mapIso
      (actionRegularH0Equiv A [φ (MvPolynomial.X 1),φ (MvPolynomial.X 0)]).toModuleIso).toLinearEquiv.trans
        (quotientCoefficientEquiv k A (endpointIdeal k A φ)))

variable (φ : MvPolynomial (Fin 2) k →ₐ[k] A)
  [Module.Finite (MvPolynomial (Fin 2) k) (polynomialRegularModule k (Fin 2) A φ)]

/-- Finite-dimensionality of the genuine endpoint quotient is proved
from E-finiteness and actual Koszul/Tor, not assumed as an Artin input. -/
noncomputable instance endpointQuotientFinite : Module.Finite k (EndpointQuotient k A φ) := by
  let J := (coefficientKoszulListFunctor k (Fin 2) [1,0]).obj (polynomialRegularModule k (Fin 2) A φ)
  let e := fullListHomologyKIso k (Fin 2) [1,0] (by intro x;fin_cases x <;> simp) (by decide)
    (polynomialRegularModule k (Fin 2) A φ) 0
  let : Module.Finite k (koszulHomologyK k (Fin 2) (polynomialRegularModule k (Fin 2) A φ) 0) :=
    koszul_homology_finite k (Fin 2) _ 0
  let : Module.Finite k (J.homology 0) := Module.Finite.equiv e.toLinearEquiv
  let : Module.Finite k ((regularPartialCoefficientComplex k A
      [φ (MvPolynomial.X 1),φ (MvPolynomial.X 0)]).homology 0) :=
    complex_homologyFinite_of_iso k (regularPartialPolynomialIso k A (Fin 2) φ [1,0]) 0
  exact Module.Finite.equiv (endpointH0QuotientEquiv k A φ)
end NSP14.Endpoint
namespace NSP14.Endpoint.Data
variable (D : NSP14.Endpoint.Data) (k : Type) [Field k]

abbrev QCore := NSP14.Endpoint.EndpointQuotient k (D.Core k) (D.endpointToCore k)
abbrev QActual := NSP14.Endpoint.EndpointQuotient k (D.source.TangentAlgebra k) (D.endpointToG k)

noncomputable def actualH0QuotientEquiv : (D.endpointComplex k).homology 0 ≃ₗ[k] D.QActual k :=
  NSP14.Endpoint.endpointH0QuotientEquiv k (D.source.TangentAlgebra k) (D.endpointToG k)

noncomputable def actualP : ℕ := Module.finrank k (D.QActual k)
noncomputable def coreP : ℕ := Module.finrank k (D.QCore k)
noncomputable def actualR : ℕ := Module.finrank k ((D.endpointComplex k).homology 2)

theorem actualH0_dimension : Module.finrank k ((D.endpointComplex k).homology 0)=D.actualP k :=
  (D.actualH0QuotientEquiv k).finrank_eq
end NSP14.Endpoint.Data
