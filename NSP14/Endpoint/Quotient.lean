module
public import NSP14.Endpoint.AssembledKernel
public import Mathlib.LinearAlgebra.Isomorphisms
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open scoped Classical DirectSum
open CategoryTheory
namespace NSP14.Endpoint.Data
variable (D : NSP14.Endpoint.Data) (k : Type) [Field k]

noncomputable def actualKernelSubmodule (r : Fin D.u) :
    Submodule (D.EndpointRing k) (D.coreFiberIdeal k r) :=
  Submodule.comap (D.coreFiberIdeal k r).subtype (D.actualKernelIdeal k r)

abbrev FiberQuotient (r : Fin D.u) := (D.coreFiberIdeal k r) ⧸ D.actualKernelSubmodule k r

noncomputable instance fiberQuotientAddCommGroup (r : Fin D.u) : AddCommGroup (D.FiberQuotient k r) :=
  inferInstanceAs (AddCommGroup ((D.coreFiberIdeal k r) ⧸ D.actualKernelSubmodule k r))

noncomputable instance fiberQuotientModuleStructure (r : Fin D.u) : Module (D.EndpointRing k) (D.FiberQuotient k r) :=
  inferInstanceAs (Module (D.EndpointRing k) ((D.coreFiberIdeal k r) ⧸ D.actualKernelSubmodule k r))

noncomputable def fiberQuotientModule : ModuleCat (D.EndpointRing k) :=
  ModuleCat.of (D.EndpointRing k) (⨁ r : Fin D.u,D.FiberQuotient k r)

noncomputable def fiberToG :
    D.fiberSumModule k →ₗ[D.EndpointRing k] D.actualEndpointModule k :=
  (D.coreToGEndpoint k).hom.comp (D.coreFiberModuleEquiv k).symm.toLinearMap

theorem fiberToG_apply (f : ⨁ r : Fin D.u,D.coreFiberIdeal k r) :
    D.fiberToG k f=D.coreToG k (D.coreFiberLinearAssembly k f) := rfl

theorem fiberToG_surjective : Function.Surjective (D.fiberToG k) :=
  (D.coreToGEndpoint_surjective k).comp (D.coreFiberModuleEquiv k).symm.surjective

noncomputable def fiberQuotientMap :
    D.fiberSumModule k →ₗ[D.EndpointRing k] D.fiberQuotientModule k :=
  DFinsupp.mapRange.linearMap (fun r => (D.actualKernelSubmodule k r).mkQ)

theorem fiberQuotientMap_surjective : Function.Surjective (D.fiberQuotientMap k) :=
  (DFinsupp.mapRange_surjective _ (fun r => (D.actualKernelSubmodule k r).mkQ.map_zero)).mpr (fun r => (D.actualKernelSubmodule k r).mkQ_surjective)

theorem fiberToG_kernel : (D.fiberToG k).ker=(D.fiberQuotientMap k).ker := by
  ext f
  change D.fiberToG k f=0 ↔ D.fiberQuotientMap k f=0
  rw [D.fiberToG_apply,D.assembled_kernel_iff]
  constructor
  · intro h
    apply DFinsupp.ext
    intro r
    change (D.actualKernelSubmodule k r).mkQ ((show (⨁ r : Fin D.u,D.coreFiberIdeal k r) from f) r)=0
    exact (Submodule.Quotient.mk_eq_zero _).mpr (h r)
  · intro h r
    have hr := congrArg (fun f : D.fiberQuotientModule k => (show (⨁ r : Fin D.u,D.FiberQuotient k r) from f) r) h
    change (D.actualKernelSubmodule k r).mkQ ((show (⨁ r : Fin D.u,D.coreFiberIdeal k r) from f) r)=0 at hr
    change (show (⨁ r : Fin D.u,D.coreFiberIdeal k r) from f) r∈D.actualKernelSubmodule k r
    exact (Submodule.Quotient.mk_eq_zero (D.actualKernelSubmodule k r)).mp hr

noncomputable def fiberToGQuotientEquiv :
    ((D.fiberSumModule k) ⧸ (D.fiberToG k).ker) ≃ₗ[D.EndpointRing k]
      D.actualEndpointModule k :=
  (D.fiberToG k).quotKerEquivOfSurjective (D.fiberToG_surjective k)

noncomputable def fiberKernelQuotientEquiv :
    ((D.fiberSumModule k) ⧸ (D.fiberToG k).ker) ≃ₗ[D.EndpointRing k]
      ((D.fiberSumModule k) ⧸ (D.fiberQuotientMap k).ker) :=
  Submodule.quotEquivOfEq (D.fiberToG k).ker (D.fiberQuotientMap k).ker (D.fiberToG_kernel k)

noncomputable def fiberQuotientAssemblyEquiv :
    ((D.fiberSumModule k) ⧸ (D.fiberQuotientMap k).ker) ≃ₗ[D.EndpointRing k]
      D.fiberQuotientModule k :=
  (D.fiberQuotientMap k).quotKerEquivOfSurjective (D.fiberQuotientMap_surjective k)

/-- The quotient pieces are the actual M_r/(M_r intersect T_r), and
this equivalence is for the same endpoint action on the same G. -/
noncomputable def actualFiberModuleEquiv :
    D.actualEndpointModule k ≃ₗ[D.EndpointRing k] D.fiberQuotientModule k :=
  (D.fiberToGQuotientEquiv k).symm.trans
    ((D.fiberKernelQuotientEquiv k).trans (D.fiberQuotientAssemblyEquiv k))

theorem actualFiberModuleEquiv_apply (f : ⨁ r : Fin D.u,D.coreFiberIdeal k r) :
    D.actualFiberModuleEquiv k (D.fiberToG k f)=D.fiberQuotientMap k f := by
  simp only [actualFiberModuleEquiv,fiberToGQuotientEquiv,fiberKernelQuotientEquiv,
    fiberQuotientAssemblyEquiv,LinearEquiv.trans_apply,
    LinearMap.quotKerEquivOfSurjective_symm_apply,
    Submodule.quotEquivOfEq_mk,LinearMap.quotKerEquivOfSurjective_apply_mk]
end NSP14.Endpoint.Data
