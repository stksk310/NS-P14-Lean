module
public import NSP14.Endpoint.Data
public import NSP14.Homological.PolynomialModules
public import NSP14.Homological.PolynomialEquivBetti
public import NSP14.Homological.PolynomialAugmentation
@[expose] public section
open scoped Classical
open NSP14.Homological CategoryTheory
namespace NSP14.Endpoint.Data
variable (D : NSP14.Endpoint.Data)

abbrev Variables := ↥D.offsets

noncomputable def atomVariable (b : D.Variables) : D.source.AtomExponent :=
  ⟨⟨D.m+b.val*D.d,D.source_generator b.val b.property⟩,D.generator_atom b.val b.property⟩

noncomputable def atomVariableEquiv : D.Variables ≃ D.source.AtomExponent :=
  Equiv.ofBijective D.atomVariable ⟨by
    intro a b h
    apply Subtype.ext
    exact D.generator_injective (congrArg (fun x : D.source.AtomExponent => x.val.val) h),by
    intro x
    obtain ⟨b,hb,he⟩ := Finset.mem_image.mp (D.atoms ▸ (D.source.mem_atoms_iff _).mpr x.property)
    exact ⟨⟨b,hb⟩,Subtype.ext (Subtype.ext he)⟩⟩

theorem variables_card : Fintype.card D.Variables=D.q+2 := by
  rw [Fintype.card_coe,D.offsets_card]

abbrev FullRing (k : Type*) [CommRing k] := MvPolynomial D.Variables k
abbrev EndpointRing (_D : NSP14.Endpoint.Data) (k : Type*) [CommRing k] := MvPolynomial (Fin 2) k
abbrev InternalRing (k : Type*) [CommRing k] := MvPolynomial D.a k

def xVariable : D.Variables := ⟨0,by simp⟩
def vVariable : D.Variables := ⟨D.u,by simp⟩
def internalVariable (b : D.a) : D.Variables := ⟨b.val,by simp [b.property]⟩
def endpointVariable (i : Fin 2) : D.Variables := if i.val=0 then D.xVariable else D.vVariable

theorem endpointVariable_injective : Function.Injective D.endpointVariable := by
  intro a b h
  have ha2 := a.isLt
  have hb2 := b.isLt
  by_cases ha : a.val=0
  · by_cases hb : b.val=0
    · apply Fin.ext;omega
    · have hv := congrArg (fun z : D.Variables => z.val) h
      simp only [endpointVariable,ha,hb,ite_true,ite_false,xVariable,vVariable] at hv
      have := D.u_pos
      omega
  · by_cases hb : b.val=0
    · have hv := congrArg (fun z : D.Variables => z.val) h
      simp only [endpointVariable,ha,hb,ite_true,ite_false,xVariable,vVariable] at hv
      have := D.u_pos
      omega
    · apply Fin.ext;omega

theorem internalVariable_injective : Function.Injective D.internalVariable := by
  intro a b h
  exact Subtype.ext (congrArg (fun z : D.Variables => z.val) h)

variable (k : Type) [Field k]
noncomputable def fullPolynomialEquiv : D.FullRing k ≃ₐ[k] D.source.FullPolynomialRing k :=
  MvPolynomial.renameEquiv k D.atomVariableEquiv

noncomputable def fullToG : D.FullRing k →ₐ[k] D.source.TangentAlgebra k :=
  (D.source.fullPolynomialToG k).comp (D.fullPolynomialEquiv k).toAlgHom

noncomputable def endpointToFull : D.EndpointRing k →ₐ[k] D.FullRing k :=
  MvPolynomial.rename D.endpointVariable

noncomputable def internalToFull : D.InternalRing k →ₐ[k] D.FullRing k :=
  MvPolynomial.rename D.internalVariable

noncomputable def endpointToG : D.EndpointRing k →ₐ[k] D.source.TangentAlgebra k :=
  (D.fullToG k).comp (D.endpointToFull k)

noncomputable def internalToG : D.InternalRing k →ₐ[k] D.source.TangentAlgebra k :=
  (D.fullToG k).comp (D.internalToFull k)

theorem fullToG_X (b : D.Variables) :
    D.fullToG k (MvPolynomial.X b)=D.source.initialMonomial k (D.atomVariable b).val := by
  change D.source.fullPolynomialToG k ((D.fullPolynomialEquiv k) (MvPolynomial.X b))=_
  rw [fullPolynomialEquiv,MvPolynomial.renameEquiv_apply,MvPolynomial.rename_X,D.source.fullPolynomialToG_X]
  rfl

theorem endpointToFull_injective : Function.Injective (D.endpointToFull k) :=
  MvPolynomial.rename_injective _ D.endpointVariable_injective

theorem internalToFull_injective : Function.Injective (D.internalToFull k) :=
  MvPolynomial.rename_injective _ D.internalVariable_injective

/-- Actual G with the same minimal variables renamed; no independent
polynomial action or unproved presentation is supplied to this module. -/
noncomputable def fullG : ModuleCat (D.FullRing k) :=
  (ModuleCat.restrictScalars (D.fullPolynomialEquiv k).toRingEquiv.toRingHom).obj
    (ModuleCat.of (D.source.FullPolynomialRing k) (D.source.TangentAlgebra k))

noncomputable instance fullG_finite : Module.Finite (D.FullRing k) (D.fullG k) :=
  polynomialEquivRestricted_finite k D.Variables D.source.AtomExponent
    (D.fullPolynomialEquiv k)
    (ModuleCat.of (D.source.FullPolynomialRing k) (D.source.TangentAlgebra k))

theorem fullG_totalBetti (i : ℕ) :
    totalBetti k D.Variables (D.fullG k) i=
      totalBetti k D.source.AtomExponent
        (ModuleCat.of (D.source.FullPolynomialRing k) (D.source.TangentAlgebra k)) i := by
  exact (polynomialEquivBettiIso k D.Variables D.source.AtomExponent
    (D.fullPolynomialEquiv k)
    (augmentation_rename k D.Variables D.source.AtomExponent D.atomVariableEquiv)
    (ModuleCat.of (D.source.FullPolynomialRing k) (D.source.TangentAlgebra k)) i).toLinearEquiv.finrank_eq
end NSP14.Endpoint.Data
