module
public import NSP14.Endpoint.MonomialAnnihilator
public import NSP14.Endpoint.SocleBounds
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open scoped Classical
namespace NSP14.Endpoint.Data
variable (D : Data)

def endpointExponent (i : Fin 2) : D.source.carrier := D.coreValue (D.coreGeneratorPoint (D.endpointVariable i))

theorem endpointExponent_order (i : Fin 2) : D.source.order (D.endpointExponent i).val=1 := by
  change D.source.order (D.coreValue (D.coreGeneratorPoint (D.endpointVariable i))).val=1
  rw [D.coreGeneratorPoint_value]
  exact D.source.atom_order (D.atomVariable (D.endpointVariable i)).property

variable (k : Type) [Field k]
theorem endpointToG_initial (i : Fin 2) : D.endpointToG k (MvPolynomial.X i)=
    D.source.initialMonomial k (D.endpointExponent i) := by
  have h := AlgHom.congr_fun (D.coreToG_endpointToCore k) (MvPolynomial.X i)
  change D.coreToG k (D.endpointToCore k (MvPolynomial.X i))=D.endpointToG k (MvPolynomial.X i) at h
  rw [D.endpointToCore_X] at h
  rw [←h,D.coreToG_monomial]
  exact D.coreInitial_live k _ (D.endpointExponent_order i).symm

abbrev EndpointSocleExponent := {a : D.source.carrier //
  ¬D.source.survivesBy (D.endpointExponent 0) a ∧ ¬D.source.survivesBy (D.endpointExponent 1) a}

theorem actualSocle_twoMonomial : D.actualSocle k=
    D.source.twoMonomialSocle k (D.endpointExponent 0) (D.endpointExponent 1) := by
  unfold actualSocle endpointMultiply NumericalSemigroup.twoMonomialSocle NumericalSemigroup.multiplyBy
  rw [D.endpointToG_initial k 0,D.endpointToG_initial k 1]

/-- Full actual endpoint-socle coordinates, with arbitrary linear
combinations and no cancellation left unchecked. -/
noncomputable def actualSocleCoordinates : D.actualSocle k ≃ₗ[k] (D.EndpointSocleExponent →₀ k) :=
  (LinearEquiv.ofEq _ _ (D.actualSocle_twoMonomial k)).trans
    (D.source.twoMonomialSocleCoordinates k (D.endpointExponent 0) (D.endpointExponent 1))

noncomputable def actualSoclePointBasis : Module.Basis D.EndpointSocleExponent k (D.actualSocle k) :=
  Finsupp.basisSingleOne.map (D.actualSocleCoordinates k).symm

instance endpointSocleExponentFinite : Finite D.EndpointSocleExponent :=
  Module.Finite.finite_basis (D.actualSoclePointBasis ℚ)

theorem actualR_exponent_count : D.actualR k=Nat.card D.EndpointSocleExponent := by
  let := Fintype.ofFinite D.EndpointSocleExponent
  rw [D.actualR_socle_dimension,Module.finrank_eq_card_basis (D.actualSoclePointBasis k),Nat.card_eq_fintype_card]
end NSP14.Endpoint.Data
