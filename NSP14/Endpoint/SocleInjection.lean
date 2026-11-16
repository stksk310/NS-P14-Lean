module
public import NSP14.Endpoint.FiberInjection
public import NSP14.Endpoint.Socle
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open scoped Classical
open CategoryTheory
namespace NSP14.Endpoint.Data
variable (D : NSP14.Endpoint.Data) (k : Type) [Field k]

theorem actualSocle_endpoint_zero (a : D.actualSocle k) (i : Fin 2) :
    (MvPolynomial.X i : D.EndpointRing k) • (show D.actualEndpointModule k from a.val)=0 := by
  change D.endpointToG k (MvPolynomial.X i)*a.val=0
  fin_cases i
  · have h : a.val*D.endpointToG k (MvPolynomial.X 0)=0 := a.property.1
    rw [mul_comm]
    exact h
  · have h : a.val*D.endpointToG k (MvPolynomial.X 1)=0 := a.property.2
    rw [mul_comm]
    exact h

theorem actualSocle_competitor_member (a : D.actualSocle k) (s : Fin D.u) :
    D.actualCompetitorProductInjection k (show D.actualEndpointModule k from a.val) s∈
      NSP14.Endpoint.coordinateSocle k (D.competitorFiber s) := by
  have he (i : Fin 2) := (D.actualCompetitorProductInjection k).map_smul
    (MvPolynomial.X i : D.EndpointRing k) (show D.actualEndpointModule k from a.val)
  have hz (i : Fin 2) :
      (MvPolynomial.X i : D.EndpointRing k) • D.actualCompetitorProductInjection k
        (show D.actualEndpointModule k from a.val) s=0 := by
    have h := he i
    rw [D.actualSocle_endpoint_zero k a i,map_zero] at h
    exact (congrArg (fun f => f s) h).symm
  constructor
  · have h := hz 0
    change Ideal.Quotient.mk (D.competitorIdeal k s) (MvPolynomial.X (0:Fin 2))*
      D.actualCompetitorProductInjection k (show D.actualEndpointModule k from a.val) s=0 at h
    change D.actualCompetitorProductInjection k (show D.actualEndpointModule k from a.val) s*
      Ideal.Quotient.mk (D.competitorIdeal k s) (MvPolynomial.X (0:Fin 2))=0
    rw [mul_comm]
    exact h
  · have h := hz 1
    change Ideal.Quotient.mk (D.competitorIdeal k s) (MvPolynomial.X (1:Fin 2))*
      D.actualCompetitorProductInjection k (show D.actualEndpointModule k from a.val) s=0 at h
    change D.actualCompetitorProductInjection k (show D.actualEndpointModule k from a.val) s*
      Ideal.Quotient.mk (D.competitorIdeal k s) (MvPolynomial.X (1:Fin 2))=0
    rw [mul_comm]
    exact h

/-- Restriction of the actual E-linear injection to actual endpoint
socles, landing in genuine monomial quotient socles. -/
noncomputable def actualSocleProductMap : D.actualSocle k →ₗ[k]
    (∀ s : Fin D.u,NSP14.Endpoint.coordinateSocle k (D.competitorFiber s)) where
  toFun a s := ⟨D.actualCompetitorProductInjection k (show D.actualEndpointModule k from a.val) s,
    D.actualSocle_competitor_member k a s⟩
  map_add' a b := by
    ext s
    exact congrArg (fun f => f s) ((D.actualCompetitorProductInjection k).map_add
      (show D.actualEndpointModule k from a.val) (show D.actualEndpointModule k from b.val))
  map_smul' c a := by
    ext s
    change D.actualCompetitorProductInjection k (show D.actualEndpointModule k from c • a.val) s=
      c • D.actualCompetitorProductInjection k (show D.actualEndpointModule k from a.val) s
    have h := (D.actualCompetitorProductInjection k).map_smul (MvPolynomial.C c)
      (show D.actualEndpointModule k from a.val)
    have hs : (MvPolynomial.C c : D.EndpointRing k) • (show D.actualEndpointModule k from a.val)=
        (show D.actualEndpointModule k from c • a.val) := by
      change D.endpointToG k (MvPolynomial.C c)*a.val=c • a.val
      have hφ : D.endpointToG k (MvPolynomial.C c)=algebraMap k (D.source.TangentAlgebra k) c := (D.endpointToG k).commutes c
      rw [hφ,Algebra.smul_def]
    rw [hs] at h
    have he := congrArg (fun f => f s) h
    change D.actualCompetitorProductInjection k (show D.actualEndpointModule k from c • a.val) s=
      (MvPolynomial.C c : D.EndpointRing k) • D.actualCompetitorProductInjection k
        (show D.actualEndpointModule k from a.val) s at he
    rw [he]
    change (algebraMap k (D.EndpointRing k) c) •
      (D.actualCompetitorProductInjection k (show D.actualEndpointModule k from a.val) s)=_
    rw [algebraMap_smul]

theorem actualSocleProductMap_injective : Function.Injective (D.actualSocleProductMap k) := by
  intro a b h
  apply Subtype.ext
  apply D.actualCompetitorProductInjection_injective k
  funext s
  exact congrArg (fun f => (f s).val) h
end NSP14.Endpoint.Data
