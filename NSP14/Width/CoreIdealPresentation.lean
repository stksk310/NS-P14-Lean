module
public import NSP14.Width.IdealGeneratorBound
public import NSP14.Endpoint.CoreAugmentation
public import NSP14.Endpoint.CoreArtinBasis
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory NSP14.Homological
attribute [local instance] MvPolynomial.gradedAlgebra
namespace NSP14.Endpoint.Data
variable (D : NSP14.Endpoint.Data) (k : Type) [Field k]

noncomputable def coreKernelPresentation :
    (D.InternalRing k ⧸ RingHom.ker (D.internalToQCore k).toRingHom) ≃ₐ[k] D.QCore k :=
  Ideal.quotientKerAlgEquivOfSurjective (D.internalToQCore_surjective k)

noncomputable def coreKernelModuleIso :
    NSP14.Endpoint.artinModule k D.a (RingHom.ker (D.internalToQCore k).toRingHom) ≅ D.QCoreModule k := by
  let e := D.coreKernelPresentation k
  let f : NSP14.Endpoint.artinModule k D.a (RingHom.ker (D.internalToQCore k).toRingHom) →ₗ[D.InternalRing k]
      D.QCoreModule k := {
    toFun a := e a
    map_add' a b := e.map_add a b
    map_smul' r a := by
      change e (Ideal.Quotient.mk _ r*a)=D.internalToQCore k r*e a
      rw [map_mul]
      rfl }
  exact LinearEquiv.toModuleIso (LinearEquiv.ofBijective f e.bijective)

/-- Actual first Tor is bounded by an actual generating family for the
actual defining kernel. No Betti comparison is supplied as a premise. -/
theorem QCore_first_le_kernel_generators {ι : Type} [Fintype ι]
    (v : ι → D.InternalRing k)
    (hker : RingHom.ker (D.internalToQCore k).toRingHom=Ideal.span (Set.range v))
    (hhom : (RingHom.ker (D.internalToQCore k).toRingHom).IsHomogeneous
      (MvPolynomial.homogeneousSubmodule D.a k)) :
    totalBetti k D.a (D.QCoreModule k) 1 ≤ Fintype.card ι := by
  let I := RingHom.ker (D.internalToQCore k).toRingHom
  let : Module.Finite k (D.InternalRing k ⧸ I) :=
    Module.Finite.equiv (D.coreKernelPresentation k).toLinearEquiv.symm
  have hproper : I≠⊤ := by
    intro hI
    have h1 : (1:D.InternalRing k)∈I := by rw [hI]; trivial
    have hφ : D.internalToQCore k 1=0 := h1
    have he := congrArg (D.QCoreAugmentation k) hφ
    have he' : (1:k)=0 := by simpa only [map_one,map_zero] using he
    exact one_ne_zero he'
  rw [←totalBetti_iso k D.a (D.coreKernelModuleIso k) 1,
    NSP14.Endpoint.artin_first_generators k D.a I hproper hhom]
  exact NSP14.Width.idealGeneratorNumber_le k D.a I v hker
end NSP14.Endpoint.Data
