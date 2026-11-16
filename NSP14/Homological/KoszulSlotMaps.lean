module
public import NSP14.Homological.KoszulChainBasis
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory HomologicalComplex
open scoped Classical
namespace NSP14.Homological
universe u
variable (k σ : Type u) [Field k] (M : ModuleCat.{u} (VariableRing k σ))

/-- The literal polynomial-linear inclusion of one coefficient-module copy
into the actual Koszul chain. -/
noncomputable def koszulSlotIn : ∀ (xs : List σ) (j : ℕ),
    KoszulSlot xs.length j → (M ⟶ (koszulList k σ xs M).X j)
  | [],0,_ => 𝟙 M
  | [],_+1,s => s.elim
  | x::xs,0,s => koszulSlotIn xs 0 s ≫
      homotopyCofiber.inrX ((MvPolynomial.X x : VariableRing k σ) • 𝟙 (koszulList k σ xs M)) 0
  | x::xs,j+1,.inl s => koszulSlotIn xs j s ≫
      homotopyCofiber.inlX ((MvPolynomial.X x : VariableRing k σ) • 𝟙 (koszulList k σ xs M)) j (j+1) (natDownStep j)
  | x::xs,j+1,.inr s => koszulSlotIn xs (j+1) s ≫
      homotopyCofiber.inrX ((MvPolynomial.X x : VariableRing k σ) • 𝟙 (koszulList k σ xs M)) (j+1)

noncomputable def koszulSlotOut : ∀ (xs : List σ) (j : ℕ),
    KoszulSlot xs.length j → ((koszulList k σ xs M).X j ⟶ M)
  | [],0,_ => 𝟙 M
  | [],_+1,s => s.elim
  | x::xs,0,s =>
      homotopyCofiber.sndX ((MvPolynomial.X x : VariableRing k σ) • 𝟙 (koszulList k σ xs M)) 0 ≫
        koszulSlotOut xs 0 s
  | x::xs,j+1,.inl s =>
      homotopyCofiber.fstX ((MvPolynomial.X x : VariableRing k σ) • 𝟙 (koszulList k σ xs M)) (j+1) j (natDownStep j) ≫
        koszulSlotOut xs j s
  | x::xs,j+1,.inr s =>
      homotopyCofiber.sndX ((MvPolynomial.X x : VariableRing k σ) • 𝟙 (koszulList k σ xs M)) (j+1) ≫
        koszulSlotOut xs (j+1) s

/-- These are actual split components, before taking any dimension/rank. -/
theorem koszulSlotIn_Out (xs : List σ) (j : ℕ) (s t : KoszulSlot xs.length j) :
    koszulSlotIn k σ M xs j s ≫ koszulSlotOut k σ M xs j t=
      if s=t then 𝟙 M else 0 := by
  classical
  induction xs generalizing j with
  | nil => cases j with
    | zero => cases s;cases t;simp [koszulSlotIn,koszulSlotOut]
    | succ j => exact s.elim
  | cons x xs ih =>
    cases j with
    | zero =>
      simp only [koszulSlotIn,koszulSlotOut,Category.assoc]
      rw [← Category.assoc (homotopyCofiber.inrX _ 0),homotopyCofiber.inrX_sndX,Category.id_comp]
      exact ih 0 s t
    | succ j =>
      cases s with
      | inl s => cases t with
        | inl t =>
          simp only [koszulSlotIn,koszulSlotOut,Category.assoc]
          rw [← Category.assoc (homotopyCofiber.inlX _ _ _ _),homotopyCofiber.inlX_fstX,Category.id_comp]
          by_cases he : s=t
          · subst t
            simpa only [ite_eq_left rfl] using ih j s s
          · rw [ite_eq_right (fun h => he (Sum.inl_injective h))]
            simpa only [ite_eq_right he] using ih j s t
        | inr t =>
          simp only [koszulSlotIn,koszulSlotOut,Category.assoc]
          rw [← Category.assoc (homotopyCofiber.inlX _ _ _ _),homotopyCofiber.inlX_sndX]
          simp
      | inr s => cases t with
        | inl t =>
          simp only [koszulSlotIn,koszulSlotOut,Category.assoc]
          rw [← Category.assoc (homotopyCofiber.inrX _ _),homotopyCofiber.inrX_fstX]
          simp
        | inr t =>
          simp only [koszulSlotIn,koszulSlotOut,Category.assoc]
          rw [← Category.assoc (homotopyCofiber.inrX _ _),homotopyCofiber.inrX_sndX,Category.id_comp]
          by_cases he : s=t
          · subst t
            simpa only [ite_eq_left rfl] using ih (j+1) s s
          · rw [ite_eq_right (fun h => he (Sum.inr_injective h))]
            simpa only [ite_eq_right he] using ih (j+1) s t
end NSP14.Homological
