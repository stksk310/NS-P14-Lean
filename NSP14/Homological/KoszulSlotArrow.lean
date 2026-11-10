module
public import NSP14.Homological.KoszulSlotDifferential
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped Classical
namespace NSP14.Homological
variable {σ : Type*}

/-- Exact signed variable in one actual Koszul differential component.
false means +X, true means -X. No field division occurs. -/
noncomputable def koszulSlotArrow : ∀ (xs : List σ) (j : ℕ),
    KoszulSlot xs.length (j+1) → KoszulSlot xs.length j → Option (σ × Bool)
  | [],_,s,_ => s.elim
  | x::_xs,0,.inl s,t => if s=t then some (x,false) else none
  | _x::xs,0,.inr s,t => koszulSlotArrow xs 0 s t
  | _x::xs,j+1,.inl s,.inl t => (koszulSlotArrow xs j s t).map (fun a => (a.1,!a.2))
  | x::_xs,_j+1,.inl s,.inr t => if s=t then some (x,false) else none
  | _x::_xs,_j+1,.inr _,.inl _ => none
  | _x::xs,j+1,.inr s,.inr t => koszulSlotArrow xs (j+1) s t

universe u
variable (k σ : Type u) [Field k] (M : ModuleCat.{u} (VariableRing k σ))

noncomputable def koszulSignedVariable : Option (σ × Bool) → (M ⟶ M)
  | none => 0
  | some (x,false) => (MvPolynomial.X x : VariableRing k σ) • 𝟙 M
  | some (x,true) => -((MvPolynomial.X x : VariableRing k σ) • 𝟙 M)

theorem koszulSignedVariable_flip (a : Option (σ × Bool)) :
    koszulSignedVariable k σ M (a.map (fun b => (b.1,!b.2)))= -koszulSignedVariable k σ M a := by
  cases a with
  | none => simp [koszulSignedVariable]
  | some a => rcases a with ⟨x,b⟩;cases b <;> simp [koszulSignedVariable]

/-- The signed incidence description is proved for the actual recursive
complex, not provided as the differential of a replacement complex. -/
theorem koszulSlot_d_arrow (xs : List σ) (j : ℕ)
    (s : KoszulSlot xs.length (j+1)) (t : KoszulSlot xs.length j) :
    koszulSlotIn k σ M xs (j+1) s ≫ (koszulList k σ xs M).d (j+1) j ≫ koszulSlotOut k σ M xs j t =
      koszulSignedVariable k σ M (koszulSlotArrow xs j s t) := by
  induction xs generalizing j with
  | nil => exact s.elim
  | cons x xs ih =>
    cases j with
    | zero =>
      cases s with
      | inl s =>
        rw [koszulSlot_d_head_zero,koszulSlotIn_Out]
        by_cases h : s=t <;> simp only [koszulSlotArrow,h,ite_true,ite_false,koszulSignedVariable,smul_zero]
      | inr s =>
        rw [koszulSlot_d_tail_zero]
        exact ih 0 s t
    | succ j =>
      cases s with
      | inl s => cases t with
        | inl t =>
          rw [koszulSlot_d_head_head,ih]
          exact (koszulSignedVariable_flip k σ M _).symm
        | inr t =>
          rw [koszulSlot_d_head_tail,koszulSlotIn_Out]
          by_cases h : s=t <;> simp only [koszulSlotArrow,h,ite_true,ite_false,koszulSignedVariable,smul_zero]
      | inr s => cases t with
        | inl t => exact koszulSlot_d_tail_head k σ M x xs j s t
        | inr t =>
          rw [koszulSlot_d_tail_tail]
          exact ih (j+1) s t
end NSP14.Homological
