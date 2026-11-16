module
public import NSP14.Endpoint.ArtinTransport
public import NSP14.Homological.ActionH0Image
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory NSP14.Homological
namespace NSP14.Endpoint.Data
variable (D : NSP14.Endpoint.Data) (k : Type) [Field k]

noncomputable def endpointH0Module : ModuleCat (D.InternalRing k) :=
  actionRestrictedH0 (D.endpointElements k) (D.internalToG k).toRingHom

/-- The internal action on native H0 agrees with the action on the
actual quotient QG, with all commuting scalars retained. -/
noncomputable def endpointH0ModuleIso : D.endpointH0Module k ≅ D.QActualModule k :=
  actionRestrictedH0Iso (D.endpointElements k) (Ideal.Quotient.mk _)
    Ideal.Quotient.mk_surjective Ideal.mk_ker (D.internalToG k).toRingHom
    (D.internalToQActual k).toRingHom rfl

noncomputable instance endpointH0ModuleFinite : Module.Finite (D.InternalRing k) (D.endpointH0Module k) :=
  Module.Finite.equiv (D.endpointH0ModuleIso k).symm.toLinearEquiv

theorem endpointH0Internal_finite (i : ℕ) : Module.Finite k
    ((actionH0SingleCoefficientComplex k (D.source.TangentAlgebra k) D.a
      (D.endpointElements k) (D.internalToG k) (variableList k D.a)).homology i) := by
  let : Module.Finite (D.InternalRing k)
      (actionRestrictedH0 (D.endpointElements k) (D.internalToG k).toRingHom) := D.endpointH0ModuleFinite k
  exact actionH0Canonical_finite k (D.source.TangentAlgebra k) D.a (D.endpointElements k) (D.internalToG k) i

theorem endpointH0Internal_betti (i : ℕ) : Module.finrank k
    ((actionH0SingleCoefficientComplex k (D.source.TangentAlgebra k) D.a
      (D.endpointElements k) (D.internalToG k) (variableList k D.a)).homology i)=
        totalBetti k D.a (D.QActualModule k) i := by
  let : Module.Finite (D.InternalRing k)
      (actionRestrictedH0 (D.endpointElements k) (D.internalToG k).toRingHom) := D.endpointH0ModuleFinite k
  rw [actionH0Canonical_betti]
  exact totalBetti_iso k D.a (D.endpointH0ModuleIso k) i
end NSP14.Endpoint.Data
