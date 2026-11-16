module
public import NSP14.Homological.KoszulSlotArrow
@[expose] public section
open scoped Classical
namespace NSP14.Homological
variable {σ : Type*}

/-- Every nonzero component removes exactly its signed variable from the
actual exterior subset. Repeated-variable lists are excluded explicitly. -/
theorem koszulSlotArrow_wedge (xs : List σ) (hx : xs.Nodup) (j : ℕ)
    (s : KoszulSlot xs.length (j+1)) (t : KoszulSlot xs.length j) (v : σ) (b : Bool)
    (h : koszulSlotArrow xs j s t=some (v,b)) :
    koszulSlotWedge xs (j+1) s=insert v (koszulSlotWedge xs j t) ∧
      v ∉ koszulSlotWedge xs j t ∧ v ∈ xs := by
  induction xs generalizing j v b with
  | nil => exact s.elim
  | cons x xs ih =>
    have hxs := List.nodup_cons.mp hx
    have hnot : ∀ n (u : KoszulSlot xs.length n),x ∉ koszulSlotWedge xs n u :=
      fun n u hm => hxs.1 (koszulSlotWedge_mem xs n u x hm)
    cases j with
    | zero => cases s with
      | inl s =>
        simp only [koszulSlotArrow] at h
        split at h
        next he =>
          have hp := Option.some.inj h
          have hv := congrArg Prod.fst hp
          change x=v at hv
          subst v
          subst t
          exact ⟨rfl,hnot 0 s,List.mem_cons_self⟩
        next => contradiction
      | inr s =>
        obtain ⟨hw,hn,hv⟩ := ih hxs.2 0 s t v b h
        exact ⟨hw,hn,List.mem_cons_of_mem _ hv⟩
    | succ j => cases s with
      | inl s => cases t with
        | inl t =>
          change (koszulSlotArrow xs j s t).map (fun a => (a.1,!a.2))=some (v,b) at h
          obtain ⟨a,ha,he⟩ := Option.map_eq_some_iff.mp h
          rcases a with ⟨u,c⟩
          have hv := congrArg Prod.fst he
          change u=v at hv
          subst v
          obtain ⟨hw,hn,hu⟩ := ih hxs.2 j s t u c ha
          have hux : u ≠ x := fun he => hxs.1 (he ▸ hu)
          refine ⟨?_,?_,List.mem_cons_of_mem _ hu⟩
          · simp only [koszulSlotWedge,hw,Finset.insert_comm]
          · simpa only [koszulSlotWedge,Finset.mem_insert,not_or] using And.intro hux hn
        | inr t =>
          simp only [koszulSlotArrow] at h
          split at h
          next he =>
            have hv := congrArg Prod.fst (Option.some.inj h)
            change x=v at hv
            subst v
            subst t
            exact ⟨rfl,hnot (j+1) s,List.mem_cons_self⟩
          next => contradiction
      | inr s => cases t with
        | inl t => simp [koszulSlotArrow] at h
        | inr t =>
          obtain ⟨hw,hn,hv⟩ := ih hxs.2 (j+1) s t v b h
          exact ⟨hw,hn,List.mem_cons_of_mem _ hv⟩

/-- Construct the actual source partner of a target wedge and a missing
variable. Its differential component is a literal signed unit times X_v. -/
theorem koszulSlot_insert_partner (xs : List σ) (j : ℕ)
    (t : KoszulSlot xs.length j) (v : σ) (hv : v ∈ xs)
    (hn : v ∉ koszulSlotWedge xs j t) :
    ∃ (s : KoszulSlot xs.length (j+1)) (b : Bool),
      koszulSlotWedge xs (j+1) s=insert v (koszulSlotWedge xs j t) ∧
      koszulSlotArrow xs j s t=some (v,b) := by
  induction xs generalizing j v with
  | nil => simp at hv
  | cons x xs ih =>
    cases j with
    | zero =>
      by_cases he : v=x
      · subst v
        refine ⟨Sum.inl t,false,rfl,?_⟩
        simp [koszulSlotArrow]
      · have hv' : v ∈ xs := (List.mem_cons.mp hv).resolve_left he
        obtain ⟨s,b,hw,ha⟩ := ih 0 t v hv' hn
        exact ⟨Sum.inr s,b,hw,ha⟩
    | succ j => cases t with
      | inl t =>
        have hvx : v ≠ x := by
          intro he
          subst v
          exact hn (Finset.mem_insert_self _ _)
        have hv' : v ∈ xs := (List.mem_cons.mp hv).resolve_left hvx
        have hn' : v ∉ koszulSlotWedge xs j t := fun h => hn (Finset.mem_insert_of_mem h)
        obtain ⟨s,b,hw,ha⟩ := ih j t v hv' hn'
        refine ⟨Sum.inl s,!b,?_,?_⟩
        · simp only [koszulSlotWedge,hw,Finset.insert_comm]
        · change (koszulSlotArrow xs j s t).map (fun a => (a.1,!a.2))=some (v,!b)
          rw [ha]
          rfl
      | inr t =>
        by_cases he : v=x
        · subst v
          refine ⟨Sum.inl t,false,rfl,?_⟩
          simp [koszulSlotArrow]
        · have hv' : v ∈ xs := (List.mem_cons.mp hv).resolve_left he
          obtain ⟨s,b,hw,ha⟩ := ih (j+1) t v hv' hn
          exact ⟨Sum.inr s,b,hw,ha⟩
end NSP14.Homological
