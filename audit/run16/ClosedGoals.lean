module
public import NSP14
@[expose] public section
open CategoryTheory NSP14 NSP14.Homological
attribute [local instance] MvPolynomial.gradedAlgebra
namespace Run16Closed
variable (D : Endpoint.Data) (k : Type) [Field k]

theorem I_NORMALIZE : D.source.embeddingDimension=D.q+2 := D.embeddingDimension

theorem E_CORE : Function.Surjective (D.coreToG k) := D.coreToG_surjective k

noncomputable def E_COORD := D.coreFiberModuleEquiv k

theorem E_KERNEL (r : Fin D.u) : D.actualDeadFiber r=D.coreFiber r∩D.competitorFiber r :=
  D.actualDeadFiber_eq_inter r

theorem E_STOP (r : Fin D.u) (c : ℕ×ℕ) : c∈D.competitorFiber r ↔
    ∃ s : Fin D.u,∃ j : ℕ,1≤j ∧ j≤(D.u-2)/2+D.u/Nat.gcd D.m D.u ∧
      ∃ b : ℕ×ℕ,Minimal (·∈D.coreFiber s) b ∧ D.shiftedResidue s j=r ∧ D.forbiddenStart s j b≤c :=
  D.competitorFiber_stopping r c

theorem E_BOUNDS : D.actualR k≤min (D.wordVolume-D.u) (D.u*(D.coreHeight-2)) := D.actualR_le_Rhat k

theorem E_HOMOLOGY : Module.finrank k ((D.endpointComplex k).homology 1)=D.actualP k+D.actualR k ∧
    D.actualR k=Module.finrank k (D.actualSocle k) :=
  ⟨D.actualH1_dimension k,D.actualR_socle_dimension k⟩

theorem E_TRANSFER (i : ℕ) : totalBetti k D.Variables (D.fullG k) i≤
    totalBetti k D.a (D.QCoreModule k) i+D.coreRemainder k i := D.actual_core_endpoint_bound k i

variable (σ : Type) [Fintype σ] [LinearOrder σ]
  (I : Ideal (MvPolynomial σ k)) [Module.Finite k (MvPolynomial σ k ⧸ I)]
  (hp : I≠⊤)

include hp in
/-- General actual Artin quotient entry; no numerical profile is substituted. -/
theorem E_ARTIN (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k))
    (hl : ∀ f∈I,f.IsHomogeneous 1 → f=0) (hq : 2≤Fintype.card σ) :
    (totalBetti k σ (Endpoint.artinModule k σ I) 1 : ℚ)≤
      Endpoint.weightedFirst (Fintype.card σ) (Endpoint.artinLimit k σ I) (Endpoint.artinHilbert k σ I hI) :=
  Endpoint.artin_first_harmonic k σ I hp hI hl hq

theorem E_ROW (i : ℕ) : totalBetti k D.Variables (D.fullG k) i≤D.endpointRowBound k i :=
  D.actual_endpoint_rows k i

theorem E_TWO (hq : D.q=2) (i : ℕ) : totalBetti k D.Variables (D.fullG k) i≤D.twoRowBound k hq i :=
  D.actual_two_all_rows k hq i
end Run16Closed
