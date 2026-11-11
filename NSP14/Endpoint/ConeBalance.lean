module
public import NSP14.Homological.EndomorphismConeBound
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits HomologicalComplex NSP14.Homological
namespace NSP14.Endpoint
universe u
variable (k : Type u) [Field k] (K : ChainComplex (ModuleCat.{u} k) ℕ) (f : K ⟶ K)
  [∀ i,Module.Finite k (K.homology i)]

/-- Euler balance for a self cone with homology supported in degrees
zero and one. Infinite chain groups are allowed throughout. -/
theorem endomorphismCone_balance (h : Module.finrank k (K.homology 2)=0) :
    Module.finrank k ((homotopyCofiber f).homology 1)=
      Module.finrank k ((homotopyCofiber f).homology 0)+Module.finrank k ((homotopyCofiber f).homology 2) := by
  let S := endomorphismConeSequence k K f
  have hS : S.ShortExact := endomorphismConeSequence_shortExact k K f
  let : ∀ i,Module.Finite k (S.X₁.homology i) := fun i => endomorphismConeFirst_finite k K f i
  let : ∀ i,Module.Finite k (S.X₃.homology i) := fun i => endomorphismConeThird_finite k K f i
  let : ∀ i,Module.Finite k (S.X₂.homology i) := fun i => endomorphismCone_homology_finite k K f i
  have h0 := homology_rank_correction_zero k S hS
  have h1 := homology_rank_correction k S hS 0
  have h2 := homology_rank_correction k S hS 1
  have hfirst (i : ℕ) : Module.finrank k (S.X₁.homology i)=Module.finrank k (K.homology i) :=
    (endomorphismConeFirstHomologyIso k K f i).toLinearEquiv.finrank_eq
  have hthird (i : ℕ) : Module.finrank k (S.X₃.homology (i+1))=Module.finrank k (K.homology i) :=
    (coneSuspensionHomologyIso k K i).toLinearEquiv.finrank_eq
  have hz0 : Module.finrank k (S.X₃.homology 0)=0 := by
    have : Subsingleton (S.X₃.homology 0) :=
      ModuleCat.subsingleton_of_isZero (coneSuspension_homology_zero k K)
    exact Module.finrank_zero_of_subsingleton
  have hz3 : Module.finrank k (hS.δ 3 2 rfl).hom.range=0 := by
    have hb := LinearMap.finrank_range_le (hS.δ 3 2 rfl).hom
    rw [hthird 2,h] at hb
    omega
  rw [hfirst 0,hz0,add_zero] at h0
  rw [hfirst 1,hthird 0] at h1
  rw [hfirst 2,hthird 1,h,hz3,add_zero,zero_add] at h2
  change Module.finrank k ((homotopyCofiber f).homology 0)+_= _ at h0
  change Module.finrank k ((homotopyCofiber f).homology 1)+_+_= _ at h1
  change Module.finrank k ((homotopyCofiber f).homology 2)+_= _ at h2
  have he0 : Module.finrank k (hS.δ (0+1) 0 rfl).hom.range=Module.finrank k (hS.δ 1 0 rfl).hom.range := rfl
  have he1 : Module.finrank k (hS.δ (0+2) (0+1) rfl).hom.range=Module.finrank k (hS.δ (1+1) 1 rfl).hom.range := rfl
  rw [he0,he1] at h1
  omega
end NSP14.Endpoint
