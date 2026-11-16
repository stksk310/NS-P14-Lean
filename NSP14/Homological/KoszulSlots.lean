module
public import NSP14.Homological.KoszulResolution
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.Fintype.Card
@[expose] public section
open scoped Classical
namespace NSP14.Homological

/-- The actual subset recursion of the existing scalar-cone Koszul chains. -/
@[reducible] def KoszulSlot : ℕ → ℕ → Type
  | 0,0 => PUnit
  | 0,_+1 => PEmpty
  | r+1,0 => KoszulSlot r 0
  | r+1,j+1 => KoszulSlot r j ⊕ KoszulSlot r (j+1)

@[reducible] instance koszulSlotFintype : ∀ r j,Fintype (KoszulSlot r j)
  | 0,0 => inferInstanceAs (Fintype PUnit)
  | 0,_+1 => inferInstanceAs (Fintype PEmpty)
  | r+1,0 => koszulSlotFintype r 0
  | r+1,j+1 => by
    have := koszulSlotFintype r j
    have := koszulSlotFintype r (j+1)
    exact inferInstanceAs (Fintype (KoszulSlot r j ⊕ KoszulSlot r (j+1)))

theorem koszulSlot_card (r j : ℕ) : Fintype.card (KoszulSlot r j)=r.choose j := by
  induction r generalizing j with
  | zero => cases j <;> rfl
  | succ r ih =>
    cases j with
    | zero => simpa only [KoszulSlot,Nat.choose_zero_right] using ih 0
    | succ j =>
      change Fintype.card (KoszulSlot r j ⊕ KoszulSlot r (j+1))=(r+1).choose (j+1)
      rw [Fintype.card_sum,ih,ih,Nat.choose_succ_succ]

variable {σ : Type*}
noncomputable def koszulSlotWedge : ∀ (xs : List σ) (j : ℕ),KoszulSlot xs.length j → Finset σ
  | [],0,_ => ∅
  | [],_j+1,s => s.elim
  | _x::xs,0,s => koszulSlotWedge xs 0 s
  | x::xs,j+1,.inl s => insert x (koszulSlotWedge xs j s)
  | _x::xs,j+1,.inr s => koszulSlotWedge xs (j+1) s

theorem koszulSlotWedge_mem (xs : List σ) (j : ℕ) (s : KoszulSlot xs.length j) :
    ∀ x ∈ koszulSlotWedge xs j s,x ∈ xs := by
  induction xs generalizing j with
  | nil => cases j with
    | zero => simp [koszulSlotWedge]
    | succ j => exact s.elim
  | cons x xs ih =>
    cases j with
    | zero =>
      intro y hy
      exact List.mem_cons_of_mem _ (ih 0 s y hy)
    | succ j =>
      cases s with
      | inl s =>
        intro y hy
        rcases Finset.mem_insert.mp hy with rfl|hy
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (ih j s y hy)
      | inr s =>
        intro y hy
        exact List.mem_cons_of_mem _ (ih (j+1) s y hy)

theorem koszulSlotWedge_card (xs : List σ) (hxs : xs.Nodup) (j : ℕ) (s : KoszulSlot xs.length j) :
    (koszulSlotWedge xs j s).card=j := by
  induction xs generalizing j with
  | nil => cases j with
    | zero => rfl
    | succ j => exact s.elim
  | cons x xs ih =>
    have hx := List.nodup_cons.mp hxs
    cases j with
    | zero => exact ih hx.2 0 s
    | succ j =>
      cases s with
      | inl s =>
        change (insert x (koszulSlotWedge xs j s)).card=j+1
        rw [Finset.card_insert_of_notMem (fun h => hx.1 (koszulSlotWedge_mem xs j s x h)),ih hx.2]
      | inr s => exact ih hx.2 (j+1) s

theorem koszulSlotWedge_injective (xs : List σ) (hxs : xs.Nodup) (j : ℕ) :
    Function.Injective (koszulSlotWedge xs j) := by
  induction xs generalizing j with
  | nil => cases j with
    | zero => intro a b _;cases a;cases b;rfl
    | succ j => exact fun a => a.elim
  | cons x xs ih =>
    have hx := List.nodup_cons.mp hxs
    have hnot : ∀ j (s : KoszulSlot xs.length j),x ∉ koszulSlotWedge xs j s :=
      fun j s h => hx.1 (koszulSlotWedge_mem xs j s x h)
    cases j with
    | zero => exact ih hx.2 0
    | succ j =>
      intro a b he
      cases a with
      | inl a => cases b with
        | inl b =>
          apply congrArg Sum.inl
          apply ih hx.2 j
          have h := congrArg (Finset.erase · x) he
          simpa only [koszulSlotWedge,Finset.erase_insert (hnot j a),Finset.erase_insert (hnot j b)] using h
        | inr b =>
          have h : x ∈ koszulSlotWedge (x::xs) (j+1) (Sum.inl a) := Finset.mem_insert_self _ _
          rw [he] at h
          exact (hnot (j+1) b h).elim
      | inr a => cases b with
        | inl b =>
          have h : x ∈ koszulSlotWedge (x::xs) (j+1) (Sum.inl b) := Finset.mem_insert_self _ _
          rw [← he] at h
          exact (hnot (j+1) a h).elim
        | inr b => exact congrArg Sum.inr (ih hx.2 (j+1) he)

/-- All j-subsets of the actual variable set. -/
def KoszulWedge (σ : Type*) (j : ℕ) := {F : Finset σ //F.card=j}

noncomputable instance koszulWedgeFintype (σ : Type*) [Fintype σ] (j : ℕ) : Fintype (KoszulWedge σ j) :=
  inferInstanceAs (Fintype {F : Finset σ //F.card=j})

theorem koszulWedge_card (σ : Type*) [Fintype σ] (j : ℕ) :
    Fintype.card (KoszulWedge σ j)=(Fintype.card σ).choose j := by
  let e : KoszulWedge σ j ≃ ↥((Finset.univ : Finset σ).powersetCard j) :=
    { toFun F := ⟨F.val,Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _,F.property⟩⟩
      invFun F := ⟨F.val,(Finset.mem_powersetCard.mp F.property).2⟩
      left_inv _ := rfl
      right_inv _ := rfl }
  rw [Fintype.card_congr e,Fintype.card_coe,Finset.card_powersetCard,Finset.card_univ]

universe u
noncomputable def koszulVariableWedgeEquiv (k σ : Type u) [Field k] [Fintype σ] (j : ℕ) :
    KoszulSlot (variableList k σ).length j ≃ KoszulWedge σ j := by
  let f : KoszulSlot (variableList k σ).length j → KoszulWedge σ j :=
    fun s => ⟨koszulSlotWedge (variableList k σ) j s,
      koszulSlotWedge_card _ (variableList_nodup k σ) _ _⟩
  apply Equiv.ofBijective f
  apply (Fintype.bijective_iff_injective_and_card f).mpr
  refine ⟨fun a b he => koszulSlotWedge_injective _ (variableList_nodup k σ) j
    (congrArg Subtype.val he),?_⟩
  rw [koszulSlot_card,koszulWedge_card,variableList_length]
end NSP14.Homological
