module
public import NSP14.Endpoint.PartialBasisKernel
public import NSP14.Endpoint.TwoInternal
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open scoped Classical
namespace NSP14.Endpoint.Data
variable (D : Data)

def internalSurvives (b : D.a) (p : D.CoreMinimalIndex) : Prop :=
  D.CoreMinimal (p.val+D.coreGeneratorPoint (D.internalVariable b))
noncomputable def internalDestination (b : D.a) : {p : D.CoreMinimalIndex // D.internalSurvives b p} → D.CoreMinimalIndex :=
  fun p => ⟨p.val.val+D.coreGeneratorPoint (D.internalVariable b),p.property⟩
theorem internalDestination_injective (b : D.a) : Function.Injective (D.internalDestination b) := by
  intro p q h
  apply Subtype.ext
  apply Subtype.ext
  have he : p.val.val+D.coreGeneratorPoint (D.internalVariable b)=q.val.val+D.coreGeneratorPoint (D.internalVariable b) :=
    congrArg Subtype.val h
  exact add_right_cancel he

variable (k : Type) [Field k]
noncomputable def internalMultiply (b : D.a) : D.QCore k →ₗ[k] D.QCore k :=
  (LinearMap.mul k _).flip (D.internalToQCore k (MvPolynomial.X b))

theorem internalMultiply_kernel (b : D.a) (a : D.QCore k) : D.internalMultiply k b a=0 ↔
    ∀ p,D.internalSurvives b p → (D.QCoreBasis k).repr a p=0 := by
  apply NSP14.Endpoint.partial_basis_kernel k D.CoreMinimalIndex (D.QCore k) (D.QCoreBasis k)
    (D.internalMultiply k b) (D.internalSurvives b) (D.internalDestination b)
    (D.internalDestination_injective b)
  intro p
  change D.QCoreBasis k p*D.internalToQCore k (MvPolynomial.X b)=_
  rw [mul_comm,D.QCore_internal_basis]
  rfl

abbrev InternalSocleIndex (hq : D.q=2) := {p : D.CoreMinimalIndex //
  ¬D.internalSurvives ((D.twoInternalEquiv hq).symm 0) p ∧
  ¬D.internalSurvives ((D.twoInternalEquiv hq).symm 1) p}

noncomputable def internalSocleCoordinates (hq : D.q=2) : D.internalSocle k hq ≃ₗ[k]
    (D.InternalSocleIndex hq →₀ k) := by
  let b := D.QCoreBasis k
  let x := (D.twoInternalEquiv hq).symm 0
  let y := (D.twoInternalEquiv hq).symm 1
  let U := Finsupp.supported k k {p : D.CoreMinimalIndex | ¬D.internalSurvives x p ∧ ¬D.internalSurvives y p}
  have he (a : D.QCore k) : a∈D.internalSocle k hq ↔ b.repr a∈U := by
    rw [Finsupp.mem_supported']
    change (D.internalMultiply k x a=0 ∧ D.internalMultiply k y a=0) ↔ _
    rw [D.internalMultiply_kernel,D.internalMultiply_kernel]
    simp only [Set.mem_ofPred_eq]
    constructor
    · intro ha p hp
      by_cases hx : D.internalSurvives x p
      · exact ha.1 p hx
      · exact ha.2 p (by tauto)
    · intro ha
      exact ⟨fun p hp => ha p (by tauto),fun p hp => ha p (by tauto)⟩
  exact (b.repr.submoduleMap (D.internalSocle k hq)).trans
    ((LinearEquiv.ofEq _ U (by
      ext f
      constructor
      · rintro ⟨a,ha,rfl⟩
        exact (he a).mp ha
      · intro hf
        exact ⟨b.repr.symm f,(he _).mpr (by simpa only [LinearEquiv.apply_symm_apply] using hf),b.repr.apply_symm_apply f⟩)).trans
      (Finsupp.supportedEquivFinsupp (R:=k) {p : D.CoreMinimalIndex | ¬D.internalSurvives x p ∧ ¬D.internalSurvives y p}))

theorem internalSigma_point_count (hq : D.q=2) : D.internalSigma k hq=Nat.card (D.InternalSocleIndex hq) := by
  let := Fintype.ofFinite (D.InternalSocleIndex hq)
  rw [internalSigma,(D.internalSocleCoordinates k hq).finrank_eq,Module.finrank_finsupp_self,Nat.card_eq_fintype_card]
end NSP14.Endpoint.Data
