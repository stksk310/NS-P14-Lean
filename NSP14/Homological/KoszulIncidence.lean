module
public import NSP14.Homological.KoszulSlotDelete
public import NSP14.Homological.KoszulIndependentImages
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open scoped Classical
namespace NSP14.Homological
universe u
variable (k σ : Type u) [Field k] [Fintype σ]

noncomputable abbrev koszulIncidenceActive (j : ℕ)
    (s : KoszulSlot (variableList k σ).length (j+1)) (t : KoszulSlot (variableList k σ).length j) : Prop :=
  (koszulSlotArrow (variableList k σ) j s t).isSome

noncomputable def koszulIncidenceEntry (j : ℕ)
    (s : KoszulSlot (variableList k σ).length (j+1)) (t : KoszulSlot (variableList k σ).length j)
    (h : koszulIncidenceActive k σ j s t) : σ × Bool :=
  (koszulSlotArrow (variableList k σ) j s t).get h

omit [Field k] in
theorem koszulIncidenceEntry_arrow (j : ℕ)
    (s : KoszulSlot (variableList k σ).length (j+1)) (t : KoszulSlot (variableList k σ).length j)
    (h : koszulIncidenceActive k σ j s t) :
    koszulSlotArrow (variableList k σ) j s t=some (koszulIncidenceEntry k σ j s t h) :=
  (Option.some_get h).symm

noncomputable def koszulRowVariable (j : ℕ) (t : KoszulSlot (variableList k σ).length j) :
    {s // koszulIncidenceActive k σ j s t} → {v : σ // v ∉ koszulSlotWedge (variableList k σ) j t} :=
  fun s => ⟨(koszulIncidenceEntry k σ j s.val t s.property).1,
    (koszulSlotArrow_wedge _ (variableList_nodup k σ) j s.val t _ _
      (koszulIncidenceEntry_arrow k σ j s.val t s.property)).2.1⟩

omit [Field k] in
theorem koszulRowVariable_injective (j : ℕ) (t : KoszulSlot (variableList k σ).length j) :
    Function.Injective (koszulRowVariable k σ j t) := by
  intro s z he
  apply Subtype.ext
  apply koszulSlotWedge_injective _ (variableList_nodup k σ) (j+1)
  have hs := (koszulSlotArrow_wedge _ (variableList_nodup k σ) j s.val t _ _
    (koszulIncidenceEntry_arrow k σ j s.val t s.property)).1
  have hz := (koszulSlotArrow_wedge _ (variableList_nodup k σ) j z.val t _ _
    (koszulIncidenceEntry_arrow k σ j z.val t z.property)).1
  rw [hs,hz]
  exact congrArg (fun v => insert v (koszulSlotWedge (variableList k σ) j t)) (congrArg Subtype.val he)

noncomputable def koszulColumnVariable (j : ℕ) (s : KoszulSlot (variableList k σ).length (j+1)) :
    {t // koszulIncidenceActive k σ j s t} → {v : σ // v ∈ koszulSlotWedge (variableList k σ) (j+1) s} :=
  fun t => ⟨(koszulIncidenceEntry k σ j s t.val t.property).1,by
    have h := (koszulSlotArrow_wedge _ (variableList_nodup k σ) j s t.val _ _
      (koszulIncidenceEntry_arrow k σ j s t.val t.property)).1
    rw [h]
    exact Finset.mem_insert_self _ _⟩

omit [Field k] in
theorem koszulColumnVariable_injective (j : ℕ) (s : KoszulSlot (variableList k σ).length (j+1)) :
    Function.Injective (koszulColumnVariable k σ j s) := by
  intro t z he
  apply Subtype.ext
  apply koszulSlotWedge_injective _ (variableList_nodup k σ) j
  have ht := koszulSlotArrow_wedge _ (variableList_nodup k σ) j s t.val _ _
    (koszulIncidenceEntry_arrow k σ j s t.val t.property)
  have hz := koszulSlotArrow_wedge _ (variableList_nodup k σ) j s z.val _ _
    (koszulIncidenceEntry_arrow k σ j s z.val z.property)
  have hv := congrArg Subtype.val he
  change (koszulIncidenceEntry k σ j s t.val t.property).1=
    (koszulIncidenceEntry k σ j s z.val z.property).1 at hv
  have het := congrArg (fun F => F.erase (koszulIncidenceEntry k σ j s t.val t.property).1) ht.1
  have hez := congrArg (fun F => F.erase (koszulIncidenceEntry k σ j s z.val z.property).1) hz.1
  have hEt := Finset.erase_insert ht.2.1
  have hEz := Finset.erase_insert hz.2.1
  have ht2 := het.trans hEt
  have hz2 := hez.trans hEz
  exact ht2.symm.trans (by rw [hv];exact hz2)

omit [Field k] in
theorem koszulRowVariable_surjective (j : ℕ) (t : KoszulSlot (variableList k σ).length j) :
    Function.Surjective (koszulRowVariable k σ j t) := by
  intro v
  obtain ⟨s,b,_,ha⟩ := koszulSlot_insert_partner (variableList k σ) j t v.val
    (mem_variableList k σ v.val) v.property
  have hs : koszulIncidenceActive k σ j s t := by simp [koszulIncidenceActive,ha]
  refine ⟨⟨s,hs⟩,?_⟩
  apply Subtype.ext
  have he := (koszulIncidenceEntry_arrow k σ j s t hs).symm.trans ha
  exact congrArg (fun a : σ × Bool => a.1) (Option.some.inj he)

theorem koszulColumnVariable_surjective (j : ℕ) (s : KoszulSlot (variableList k σ).length (j+1)) :
    Function.Surjective (koszulColumnVariable k σ j s) := by
  intro v
  obtain ⟨t,b,_,ha⟩ := koszulSlot_delete_partner k σ j s v.val v.property
  have ht : koszulIncidenceActive k σ j s t := by simp [koszulIncidenceActive,ha]
  refine ⟨⟨t,ht⟩,?_⟩
  apply Subtype.ext
  have he := (koszulIncidenceEntry_arrow k σ j s t ht).symm.trans ha
  exact congrArg (fun a : σ × Bool => a.1) (Option.some.inj he)
end NSP14.Homological
