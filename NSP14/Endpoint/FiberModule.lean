module
public import NSP14.Endpoint.FiberAction
public import Mathlib.LinearAlgebra.DirectSum.Finite
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open scoped Classical DirectSum
open CategoryTheory NSP14.Homological
namespace NSP14.Endpoint.Data
variable (D : NSP14.Endpoint.Data) (k : Type) [Field k]

noncomputable def fiberSumModule : ModuleCat (D.EndpointRing k) :=
  ModuleCat.of (D.EndpointRing k) (⨁ r : Fin D.u,D.coreFiberIdeal k r)

noncomputable def coreFiberCoefficientEquiv :
    coefficientModule k (Fin 2) (D.fiberSumModule k) ≃ₗ[k]
      coefficientModule k (Fin 2) (D.coreEndpointModule k) :=
  (originalCoefficientEquiv k (Fin 2) (⨁ r : Fin D.u,D.coreFiberIdeal k r)).trans
    ((D.coreFiberLinearAssembly k).trans (D.coreEndpointCoefficients k).symm)

theorem coreFiberCoefficient_variable (i : Fin 2)
    (a : coefficientModule k (Fin 2) (D.fiberSumModule k)) :
    D.coreFiberCoefficientEquiv k ((MvPolynomial.X i : D.EndpointRing k) • a)=
      (MvPolynomial.X i : D.EndpointRing k) • D.coreFiberCoefficientEquiv k a := by
  apply (D.coreEndpointCoefficients k).injective
  rw [D.coreEndpoint_variable]
  change D.coreFiberLinearAssembly k ((MvPolynomial.X i : D.EndpointRing k) •
    (show (⨁ r : Fin D.u,D.coreFiberIdeal k r) from a))=
      D.coreMonomial k (D.coreGeneratorPoint (D.endpointVariable i))*
        D.coreFiberLinearAssembly k (show (⨁ r : Fin D.u,D.coreFiberIdeal k r) from a)
  exact D.coreFiberAssembly_variable k i _

noncomputable def coreFiberAssembly : D.fiberSumModule k ⟶ D.coreEndpointModule k :=
  polynomialHomOfVariables k (Fin 2) (D.coreFiberCoefficientEquiv k).toLinearMap
    (D.coreFiberCoefficient_variable k)

/-- The actual E-module decomposition, with each component a genuine
ideal M_r. The monomial degree is L+K+epsilon_r, retained by its index. -/
noncomputable def coreFiberModuleEquiv : D.coreEndpointModule k ≃ₗ[D.EndpointRing k]
    (⨁ r : Fin D.u,D.coreFiberIdeal k r) :=
  (LinearEquiv.ofBijective (D.coreFiberAssembly k).hom (D.coreFiberCoefficientEquiv k).bijective).symm

noncomputable instance coreEndpointFinite : Module.Finite (D.EndpointRing k) (D.coreEndpointModule k) :=
  Module.Finite.equiv (D.coreFiberModuleEquiv k).symm

noncomputable instance actualEndpointFinite : Module.Finite (D.EndpointRing k) (D.actualEndpointModule k) :=
  Module.Finite.of_surjective (D.coreToGEndpoint k).hom (D.coreToGEndpoint_surjective k)
end NSP14.Endpoint.Data
