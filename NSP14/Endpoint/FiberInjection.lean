module
public import NSP14.Endpoint.Quotient
public import NSP14.Endpoint.CompetitorBounds
public import NSP14.Endpoint.MonomialSocle
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open scoped Classical DirectSum
open CategoryTheory
namespace NSP14.Endpoint.Data
variable (D : NSP14.Endpoint.Data) (k : Type) [Field k]

abbrev CompetitorQuotient (s : Fin D.u) := D.EndpointRing k ⧸ D.competitorIdeal k s

noncomputable def fiberToCompetitor (s : Fin D.u) :
    (D.coreFiberIdeal k s) →ₗ[D.EndpointRing k] D.CompetitorQuotient k s :=
  (D.competitorIdeal k s).mkQ.comp (D.coreFiberIdeal k s).subtype

theorem fiberToCompetitor_kernel (s : Fin D.u) :
    (D.fiberToCompetitor k s).ker=D.actualKernelSubmodule k s := by
  ext a
  change Submodule.Quotient.mk a.val=0 ↔ a.val∈D.actualKernelIdeal k s
  rw [Submodule.Quotient.mk_eq_zero,D.actualKernelIdeal_eq_inf,Ideal.mem_inf]
  exact ⟨fun h => ⟨a.property,h⟩,fun h => h.2⟩

noncomputable def fiberCompetitorInjection (s : Fin D.u) :
    D.FiberQuotient k s →ₗ[D.EndpointRing k] D.CompetitorQuotient k s :=
  (D.actualKernelSubmodule k s).liftQ (D.fiberToCompetitor k s)
    (by rw [D.fiberToCompetitor_kernel])

theorem fiberCompetitorInjection_injective (s : Fin D.u) :
    Function.Injective (D.fiberCompetitorInjection k s) := by
  apply LinearMap.ker_eq_bot.mp
  exact Submodule.ker_liftQ_eq_bot _ _ _ (by rw [D.fiberToCompetitor_kernel])

noncomputable def fiberCompetitorProductMap : D.fiberQuotientModule k →ₗ[D.EndpointRing k]
    (∀ s : Fin D.u,D.CompetitorQuotient k s) where
  toFun a s := D.fiberCompetitorInjection k s ((show (⨁ s : Fin D.u,D.FiberQuotient k s) from a) s)
  map_add' a b := by ext s;exact (D.fiberCompetitorInjection k s).map_add _ _
  map_smul' p a := by ext s;exact (D.fiberCompetitorInjection k s).map_smul p _

theorem fiberCompetitorProductMap_injective : Function.Injective (D.fiberCompetitorProductMap k) := by
  intro a b h
  apply DFinsupp.ext
  intro s
  exact D.fiberCompetitorInjection_injective k s (congrArg (fun f => f s) h)

/-- The injection uses M/(M intersect T) -> E/T in each component.
No Artin hypothesis is imposed on E/T. -/
noncomputable def actualCompetitorProductInjection : D.actualEndpointModule k →ₗ[D.EndpointRing k]
    (∀ s : Fin D.u,D.CompetitorQuotient k s) :=
  (D.fiberCompetitorProductMap k).comp (D.actualFiberModuleEquiv k).toLinearMap

theorem actualCompetitorProductInjection_injective : Function.Injective (D.actualCompetitorProductInjection k) :=
  (D.fiberCompetitorProductMap_injective k).comp (D.actualFiberModuleEquiv k).injective
end NSP14.Endpoint.Data
