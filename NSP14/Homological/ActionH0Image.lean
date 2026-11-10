module
public import NSP14.Homological.ActionH0Ideal
public import Mathlib.RingTheory.Ideal.Quotient.Operations
@[expose] public section
open CategoryTheory
namespace NSP14.Homological
universe u
variable {R S : Type u} [CommRing R] [CommRing S]

noncomputable def regularImageModule (φ : R →+* S) : ModuleCat R :=
  (ModuleCat.restrictScalars φ).obj (ModuleCat.of S S)

/-- An explicit image of the native quotient, still linear over all R. -/
noncomputable def quotientImageEquiv (φ : R →+* S) (hφ : Function.Surjective φ)
    (I : Ideal R) (hI : RingHom.ker φ=I) : (R ⧸ I) ≃ₗ[R] regularImageModule φ := by
  let e : (R ⧸ I) ≃+* S := (Ideal.quotEquivOfEq hI.symm).trans (RingHom.quotientKerEquivOfSurjective hφ)
  have he (r : R) : e (Ideal.Quotient.mk I r)=φ r := by
    simp only [e,RingEquiv.trans_apply,Ideal.quotEquivOfEq_mk]
    rfl
  exact
    { toFun a := e a
      invFun b := e.symm b
      left_inv a := e.symm_apply_apply a
      right_inv b := e.apply_symm_apply b
      map_add' a b := e.map_add a b
      map_smul' r a := by
        change e (Ideal.Quotient.mk I r*a)=φ r*e a
        rw [map_mul,he] }

/-- H0 carries precisely the action induced by the surjection, with
no dimension or finiteness assumption on the native ring. -/
noncomputable def actionRegularH0ImageEquiv (rs : List R) (φ : R →+* S)
    (hφ : Function.Surjective φ) (hI : RingHom.ker φ=Ideal.span {a | a∈rs}) :
    (actionRegularComplex R rs).homology 0 ≃ₗ[R] regularImageModule φ :=
  (actionRegularH0Equiv R rs).trans (quotientImageEquiv φ hφ _ hI)

variable {T : Type u} [CommRing T]
noncomputable def actionRestrictedH0 (rs : List R) (ψ : T →+* R) : ModuleCat T :=
  (ModuleCat.restrictScalars ψ).obj ((actionRegularComplex R rs).homology 0)

noncomputable def actionRestrictedH0Iso (rs : List R) (φ : R →+* S)
    (hφ : Function.Surjective φ) (hI : RingHom.ker φ=Ideal.span {a | a∈rs})
    (ψ : T →+* R) (χ : T →+* S) (hχ : χ=φ.comp ψ) :
    actionRestrictedH0 rs ψ ≅ regularImageModule χ :=
  (ModuleCat.restrictScalars ψ).mapIso (actionRegularH0ImageEquiv rs φ hφ hI).toModuleIso ≪≫
    (ModuleCat.restrictScalarsComp'App ψ φ χ hχ (ModuleCat.of S S)).symm
end NSP14.Homological
