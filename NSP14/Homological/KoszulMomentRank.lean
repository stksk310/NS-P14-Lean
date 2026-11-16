module
public import NSP14.Homological.RankOneIncidence
public import NSP14.Homological.VandermondeSpark
public import NSP14.Homological.KoszulIncidence
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators Classical
namespace NSP14.Homological
universe u
variable (k σ : Type u) [Field k] [Fintype σ] (points : σ → k)

noncomputable def koszulMomentFunctional (d j : ℕ)
    (s : KoszulSlot (variableList k σ).length (j+1)) (t : KoszulSlot (variableList k σ).length j) :
    (Fin d → k) →ₗ[k] k :=
  match koszulSlotArrow (variableList k σ) j s t with
  | none => 0
  | some (v,b) => (if b then (-1 : k) else 1) • momentFunctional k d (points v)

noncomputable def koszulMomentImage (n j : ℕ)
    (s : KoszulSlot (variableList k σ).length (j+1)) (t : KoszulSlot (variableList k σ).length j) : Fin n → k :=
  match koszulSlotArrow (variableList k σ) j s t with
  | none => 0
  | some (v,_) => fun a => points v^a.val

noncomputable def koszulMomentMap (d n j : ℕ) :
    (KoszulSlot (variableList k σ).length (j+1) → (Fin d → k)) →ₗ[k]
      (KoszulSlot (variableList k σ).length j → (Fin n → k)) :=
  rankOneIncidence k _ _ _ _ (koszulIncidenceActive k σ j)
    (koszulMomentFunctional k σ points d j) (koszulMomentImage k σ points n j)

theorem koszulMomentFunctional_active (d j : ℕ)
    (s : KoszulSlot (variableList k σ).length (j+1)) (t : KoszulSlot (variableList k σ).length j)
    (h : koszulIncidenceActive k σ j s t) :
    koszulMomentFunctional k σ points d j s t=
      (if (koszulIncidenceEntry k σ j s t h).2 then (-1 : k) else 1) •
        momentFunctional k d (points (koszulIncidenceEntry k σ j s t h).1) := by
  unfold koszulMomentFunctional
  rw [koszulIncidenceEntry_arrow k σ j s t h]

theorem koszulMomentImage_active (n j : ℕ)
    (s : KoszulSlot (variableList k σ).length (j+1)) (t : KoszulSlot (variableList k σ).length j)
    (h : koszulIncidenceActive k σ j s t) :
    koszulMomentImage k σ points n j s t=
      (fun a : Fin n => points (koszulIncidenceEntry k σ j s t h).1^a.val) := by
  unfold koszulMomentImage
  rw [koszulIncidenceEntry_arrow k σ j s t h]

/-- Maximal-rank half above the critical exterior degree. The entries
use the signs of the actual recursive Koszul complex. -/
theorem koszulMomentMap_injective (hp : Function.Injective points) (d n j : ℕ)
    (hrow : Fintype.card σ-j ≤ n) (hcol : d ≤ j+1) :
    Function.Injective (koszulMomentMap k σ points d n j) := by
  apply rankOneIncidence_injective
  · intro t
    let P := {v : σ // v ∉ koszulSlotWedge (variableList k σ) j t}
    have hc : Fintype.card P ≤ n := by
      rw [Fintype.card_subtype_compl,Fintype.card_coe,
        koszulSlotWedge_card _ (variableList_nodup k σ)]
      exact hrow
    have hi := momentVectors_independent k (fun v : P => points v.val)
      (hp.comp Subtype.val_injective) hc
    have h := hi.comp (koszulRowVariable k σ j t) (koszulRowVariable_injective k σ j t)
    convert h using 1
    funext s
    exact koszulMomentImage_active k σ points n j s.val t s.property
  · intro s c hc
    let P := {v : σ // v ∈ koszulSlotWedge (variableList k σ) (j+1) s}
    apply momentFunctional_separate k (fun v : P => points v.val) (hp.comp Subtype.val_injective)
      (by rw [Fintype.card_coe,koszulSlotWedge_card _ (variableList_nodup k σ)];exact hcol)
    intro v
    obtain ⟨t,ht⟩ := koszulColumnVariable_surjective k σ j s v
    have hz := hc t.val t.property
    rw [koszulMomentFunctional_active k σ points d j s t.val t.property] at hz
    have hv := congrArg Subtype.val ht
    change (koszulIncidenceEntry k σ j s t.val t.property).1=v.val at hv
    rw [hv] at hz
    cases hb : (koszulIncidenceEntry k σ j s t.val t.property).2 <;>
      simpa [hb] using hz

/-- The dual maximal-rank half below the critical exterior degree. -/
theorem koszulMomentMap_surjective (hp : Function.Injective points) (d n j : ℕ)
    (hrow : n ≤ Fintype.card σ-j) (hcol : j+1 ≤ d) :
    Function.Surjective (koszulMomentMap k σ points d n j) := by
  apply rankOneIncidence_surjective
  · intro s
    let P := {v : σ // v ∈ koszulSlotWedge (variableList k σ) (j+1) s}
    have hc : Fintype.card P ≤ d := by
      rw [Fintype.card_coe,koszulSlotWedge_card _ (variableList_nodup k σ)]
      exact hcol
    have hi := momentFunctional_independent k (fun v : P => points v.val)
      (hp.comp Subtype.val_injective) hc
    have h := hi.comp (koszulColumnVariable k σ j s) (koszulColumnVariable_injective k σ j s)
    let w : {t // koszulIncidenceActive k σ j s t} → kˣ :=
      fun t => if (koszulIncidenceEntry k σ j s t.val t.property).2 then -1 else 1
    have hh := h.units_smul w
    convert hh using 1
    funext t
    rw [koszulMomentFunctional_active k σ points d j s t.val t.property]
    cases hb : (koszulIncidenceEntry k σ j s t.val t.property).2 <;> simp [w,hb,koszulColumnVariable]
    change (-1 : k) • momentFunctional k d (points (koszulIncidenceEntry k σ j s t.val t.property).1)=_
    exact neg_one_smul k (momentFunctional k d (points (koszulIncidenceEntry k σ j s t.val t.property).1))
  · intro t f hc
    let P := {v : σ // v ∉ koszulSlotWedge (variableList k σ) j t}
    apply momentVectors_dual_separate k (fun v : P => points v.val) (hp.comp Subtype.val_injective)
      (by rw [Fintype.card_subtype_compl,Fintype.card_coe,
        koszulSlotWedge_card _ (variableList_nodup k σ)];exact hrow)
    intro v
    obtain ⟨s,hs⟩ := koszulRowVariable_surjective k σ j t v
    have hz := hc s.val s.property
    rw [koszulMomentImage_active k σ points n j s.val t s.property] at hz
    have hv := congrArg Subtype.val hs
    change (koszulIncidenceEntry k σ j s.val t s.property).1=v.val at hv
    rw [hv] at hz
    exact hz

/-- Critical Hankel/Koszul block: a literal isomorphism over any field
with the indicated distinct evaluation points. -/
theorem koszulMomentMap_bijective (hp : Function.Injective points) (d n : ℕ)
    (hd : 1 ≤ d) (hcard : d+n=Fintype.card σ+1) :
    Function.Bijective (koszulMomentMap k σ points d n (d-1)) :=
  ⟨koszulMomentMap_injective k σ points hp d n (d-1) (by omega) (by omega),
   koszulMomentMap_surjective k σ points hp d n (d-1) (by omega) (by omega)⟩
end NSP14.Homological
