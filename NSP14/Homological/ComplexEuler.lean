module
public import NSP14.Homological.RankEuler
@[expose] public section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
namespace NSP14.Homological
universe u
variable (k : Type u) [Field k]

/-- Euler uses finite homology, never a finrank of an infinite chain group. -/
noncomputable def complexEuler (K : ChainComplex (ModuleCat.{u} k) ℕ) (j : ℕ) : ℤ :=
  partialEuler (fun i => Module.finrank k (K.homology i)) j

theorem complexEuler_zero (K : ChainComplex (ModuleCat.{u} k) ℕ) :
    complexEuler k K 0=Module.finrank k (K.homology 0) := rfl

theorem complexEuler_succ (K : ChainComplex (ModuleCat.{u} k) ℕ) (j : ℕ) :
    complexEuler k K (j+1)=(Module.finrank k (K.homology (j+1)) : ℤ)-complexEuler k K j := rfl

theorem complexEuler_congr {K L : ChainComplex (ModuleCat.{u} k) ℕ}
    (h : ∀ i,Module.finrank k (K.homology i)=Module.finrank k (L.homology i)) (j : ℕ) :
    complexEuler k K j=complexEuler k L j :=
  congrArg (fun b => partialEuler b j) (funext h)

theorem complexEuler_iso {K L : ChainComplex (ModuleCat.{u} k) ℕ} (e : K ≅ L) (j : ℕ) :
    complexEuler k K j=complexEuler k L j := by
  apply complexEuler_congr k _ j
  intro i
  let eH : K.homology i ≅ L.homology i :=
    (homologyFunctor (ModuleCat k) (ComplexShape.down ℕ) i).mapIso e
  exact eH.toLinearEquiv.finrank_eq

noncomputable def complexConnectingRank
    (S : ShortComplex (ChainComplex (ModuleCat.{u} k) ℕ)) (hS : S.ShortExact) (j : ℕ) : ℕ :=
  Module.finrank k (hS.δ (j+1) j rfl).hom.range

variable (S : ShortComplex (ChainComplex (ModuleCat.{u} k) ℕ)) (hS : S.ShortExact)
  [∀ i,Module.Finite k (S.X₁.homology i)] [∀ i,Module.Finite k (S.X₃.homology i)]

include hS in
theorem complexEuler_shortExact (j : ℕ) :
    complexEuler k S.X₂ j=complexEuler k S.X₁ j+complexEuler k S.X₃ j-
      (complexConnectingRank k S hS j : ℤ) := by
  let : ∀ i,Module.Finite k (S.X₂.homology i) := fun i => homology_finite_of_ends k S hS i
  induction j with
  | zero =>
    have h := homology_rank_correction_zero k S hS
    change Module.finrank k (S.X₂.homology 0)+complexConnectingRank k S hS 0=
      Module.finrank k (S.X₁.homology 0)+Module.finrank k (S.X₃.homology 0) at h
    simp only [complexEuler_zero] at h ⊢
    omega
  | succ j ih =>
    have h := homology_rank_correction k S hS j
    change Module.finrank k (S.X₂.homology (j+1))+complexConnectingRank k S hS j+
      complexConnectingRank k S hS (j+1)=Module.finrank k (S.X₁.homology (j+1))+
        Module.finrank k (S.X₃.homology (j+1)) at h
    rw [complexEuler_succ,complexEuler_succ,complexEuler_succ,ih]
    omega

include hS in
theorem complexEuler_middle_le (j : ℕ) :
    complexEuler k S.X₂ j ≤ complexEuler k S.X₁ j+complexEuler k S.X₃ j := by
  rw [complexEuler_shortExact k S hS j]
  omega
end NSP14.Homological
