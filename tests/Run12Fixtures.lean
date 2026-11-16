module

public import NSP14

@[expose] public section

noncomputable section
open NSP14 NSP14.NumericalSemigroup
open scoped BigOperators

namespace Run12Fixtures

/-- A bounded superadditive weight gives a certified upper bound on all positive-factor lengths. -/
theorem length_weight_bound (S : NumericalSemigroup) (M : ℕ) (b : ℕ → ℕ)
    (hstep : ∀ x ∈ S, 0<x → ∀ y ∈ S, x+y≤M → b y+1≤b (x+y))
    {n x : ℕ} (h : S.HasLength x n) (hx : x≤M) : n≤b x := by
  obtain ⟨f,hf,he⟩ := h
  induction n generalizing x with
  | zero => omega
  | succ n ih =>
    let y := ∑ i : Fin n, f i.succ
    have hy : y ∈ S := S.carrier.sum_mem (fun i _ => (hf i.succ).1)
    have he' : f 0+y=x := by simpa only [Fin.sum_univ_succ] using he
    have hb := ih (x := y) (by omega) (fun i => f i.succ) (fun i => hf i.succ) rfl
    have hs := hstep (f 0) (hf 0).1 (hf 0).2 y hy (by omega)
    rw [he'] at hs
    omega

def allowed : Finset ℕ := {0,9,10,15,18,19,20,24,25,26,27,28,29,30}

def changing : NumericalSemigroup where
  carrier :=
    { carrier := {n | n ∈ allowed ∨ 33≤n}
      zero_mem' := Or.inl (by decide)
      add_mem' := by
        intro x y hx hy
        change (x+y ∈ allowed ∨ 33≤x+y)
        change (x ∈ allowed ∨ 33≤x) at hx
        change (y ∈ allowed ∨ 33≤y) at hy
        simp only [allowed,Finset.mem_insert,Finset.mem_singleton] at hx hy ⊢
        omega }
  conductor := 33
  cofinite _ h := Or.inr h

theorem changing_m : changing.multiplicity=9 := by
  apply changing.multiplicity_eq (by decide) (show 9 ∈ changing from Or.inl (by decide))
  intro x hx hp
  change (x ∈ allowed ∨ 33≤x) at hx
  simp only [allowed,Finset.mem_insert,Finset.mem_singleton] at hx
  omega

def weight (n : ℕ) : ℕ := [0,0,0,0,0,0,0,0,0,1,1,0,0,0,0,1,0,0,2,2,2,0,0,0,2,2,1,3,3,3,3,0,0,3,3,3,4,4,4,4,4,2,4,4,4,5,5,5,5,5,5][n]?.getD 0

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem weight_step : ∀ x ∈ Finset.range 51, ∀ y ∈ Finset.range 51,
    (x ∈ allowed ∨ 33≤x) → 0<x → (y ∈ allowed ∨ 33≤y) → x+y≤50 →
      weight y+1≤weight (x+y) := by decide

theorem changing_order_le (x : ℕ) (hx : x ∈ changing) (hm : x≤50) : changing.order x≤weight x := by
  apply length_weight_bound changing 50 weight ?_ (changing.order_length hx) hm
  intro a ha hp b hb hab
  exact weight_step a (Finset.mem_range.mpr (by omega)) b (Finset.mem_range.mpr (by omega)) ha hp hb hab

def exp (n : ℕ) (h : n ∈ allowed ∨ 33≤n) : changing.carrier := ⟨n,h⟩
def v9 := exp 9 (Or.inl (by decide))
def v10 := exp 10 (Or.inl (by decide))
def v15 := exp 15 (Or.inl (by decide))
def v26 := exp 26 (Or.inl (by decide))
def v35 := exp 35 (Or.inr (by decide))
def v41 := exp 41 (Or.inr (by decide))
def v50 := exp 50 (Or.inr (by decide))

theorem order_15 : changing.order 15=1 := by
  have h := changing_order_le 15 v15.property (by decide)
  norm_num [weight] at h
  have hp : 1≤changing.order 15 := changing.order_pos v15.property (by decide)
  omega

theorem order_26 : changing.order 26=1 := by
  have h := changing_order_le 26 v26.property (by decide)
  norm_num [weight] at h
  have hp : 1≤changing.order 26 := changing.order_pos v26.property (by decide)
  omega

theorem order_35 : changing.order 35=3 := by
  have h := changing_order_le 35 v35.property (by decide)
  norm_num [weight] at h
  have hl := changing.length_le_order
    (show changing.HasLength 35 3 from
      ⟨![10,10,15], by intro i; fin_cases i <;> exact ⟨by first | exact v10.property | exact v15.property,by decide⟩,
        by norm_num [Fin.sum_univ_succ]⟩)
  omega

theorem order_41 : changing.order 41=2 := by
  have h := changing_order_le 41 v41.property (by decide)
  norm_num [weight] at h
  have hl := changing.length_le_order
    (show changing.HasLength 41 2 from
      ⟨![26,15], by intro i; fin_cases i <;> exact ⟨by first | exact v26.property | exact v15.property,by decide⟩,
        by norm_num [Fin.sum_univ_succ]⟩)
  omega

theorem order_50 : changing.order 50=5 := by
  have h := changing_order_le 50 v50.property (by decide)
  norm_num [weight] at h
  have hl := changing.length_le_order
    (show changing.HasLength 50 5 from ⟨fun _ => 10,fun _ => ⟨v10.property,by norm_num⟩,by norm_num⟩)
  omega

theorem terminal_26 : changing.Terminal 26 := by
  refine ⟨v26.property,?_⟩
  rw [changing_m,order_26]
  change 2<changing.order 35
  rw [order_35]; decide

theorem terminal_41 : changing.Terminal 41 := by
  refine ⟨v41.property,?_⟩
  rw [changing_m,order_41]
  change 3<changing.order 50
  rw [order_50]; decide

theorem jump_26 : changing.jump 26=2 := by
  change changing.order (26+changing.multiplicity)-changing.order 26=2
  rw [changing_m,order_26]
  change changing.order 35-1=2
  rw [order_35]

theorem jump_41 : changing.jump 41=3 := by
  change changing.order (41+changing.multiplicity)-changing.order 41=3
  rw [changing_m,order_41]
  change changing.order 50-2=3
  rw [order_50]

end Run12Fixtures
