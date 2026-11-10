module
public import NSP14.Homological.KoszulSlotMaps
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped Classical
namespace NSP14.Homological
universe u
variable (k σ : Type u) [Field k] (M : ModuleCat.{u} (VariableRing k σ))

theorem koszulSlot_d_head_head (x : σ) (xs : List σ) (j : ℕ)
    (s : KoszulSlot xs.length (j+1)) (t : KoszulSlot xs.length j) :
    koszulSlotIn k σ M (x::xs) (j+2) (.inl s) ≫ (koszulList k σ (x::xs) M).d (j+2) (j+1) ≫
      koszulSlotOut k σ M (x::xs) (j+1) (.inl t) =
    -(koszulSlotIn k σ M xs (j+1) s ≫ (koszulList k σ xs M).d (j+1) j ≫ koszulSlotOut k σ M xs j t) := by
  simp only [koszulSlotIn,koszulSlotOut,Category.assoc]
  erw [homotopyCofiber.d_fstX_assoc _ (j+2) (j+1) j (natDownStep (j+1)) (natDownStep j)]
  simp only [Preadditive.comp_neg,Preadditive.neg_comp,Category.assoc,
    homotopyCofiber.inlX_fstX_assoc]

theorem koszulSlot_d_tail_head (x : σ) (xs : List σ) (j : ℕ)
    (s : KoszulSlot xs.length (j+2)) (t : KoszulSlot xs.length j) :
    koszulSlotIn k σ M (x::xs) (j+2) (.inr s) ≫ (koszulList k σ (x::xs) M).d (j+2) (j+1) ≫
      koszulSlotOut k σ M (x::xs) (j+1) (.inl t) = 0 := by
  simp only [koszulSlotIn,koszulSlotOut,Category.assoc]
  erw [homotopyCofiber.d_fstX_assoc _ (j+2) (j+1) j (natDownStep (j+1)) (natDownStep j)]
  simp only [Preadditive.comp_neg,Preadditive.neg_comp,Category.assoc,
    homotopyCofiber.inrX_fstX_assoc,zero_comp,comp_zero,neg_zero]

theorem koszulSlot_d_tail_tail (x : σ) (xs : List σ) (j : ℕ)
    (s : KoszulSlot xs.length (j+2)) (t : KoszulSlot xs.length (j+1)) :
    koszulSlotIn k σ M (x::xs) (j+2) (.inr s) ≫ (koszulList k σ (x::xs) M).d (j+2) (j+1) ≫
      koszulSlotOut k σ M (x::xs) (j+1) (.inr t) =
    koszulSlotIn k σ M xs (j+2) s ≫ (koszulList k σ xs M).d (j+2) (j+1) ≫ koszulSlotOut k σ M xs (j+1) t := by
  simp only [koszulSlotIn,koszulSlotOut,Category.assoc]
  erw [homotopyCofiber.inrX_d_assoc]
  simp only [homotopyCofiber.inrX_sndX_assoc]

theorem koszulSlot_d_head_tail (x : σ) (xs : List σ) (j : ℕ)
    (s t : KoszulSlot xs.length (j+1)) :
    koszulSlotIn k σ M (x::xs) (j+2) (.inl s) ≫ (koszulList k σ (x::xs) M).d (j+2) (j+1) ≫
      koszulSlotOut k σ M (x::xs) (j+1) (.inr t) =
    (MvPolynomial.X x : VariableRing k σ) • (koszulSlotIn k σ M xs (j+1) s ≫ koszulSlotOut k σ M xs (j+1) t) := by
  let K := koszulList k σ xs M
  let φ : K ⟶ K := (MvPolynomial.X x : VariableRing k σ) • 𝟙 K
  change koszulSlotIn k σ M xs (j+1) s ≫ homotopyCofiber.inlX φ (j+1) (j+2) (natDownStep (j+1)) ≫
    (homotopyCofiber φ).d (j+2) (j+1) ≫ homotopyCofiber.sndX φ (j+1) ≫
      koszulSlotOut k σ M xs (j+1) t = _
  erw [homotopyCofiber.d_sndX_assoc φ (j+2) (j+1) (natDownStep (j+1))]
  simp only [Preadditive.comp_add,Preadditive.add_comp,Category.assoc,homotopyCofiber.inlX_fstX_assoc,
    homotopyCofiber.inlX_sndX_assoc,zero_comp,add_zero]
  simp [φ]

theorem koszulSlot_d_head_zero (x : σ) (xs : List σ)
    (s t : KoszulSlot xs.length 0) :
    koszulSlotIn k σ M (x::xs) 1 (.inl s) ≫ (koszulList k σ (x::xs) M).d 1 0 ≫
      koszulSlotOut k σ M (x::xs) 0 t =
    (MvPolynomial.X x : VariableRing k σ) • (koszulSlotIn k σ M xs 0 s ≫ koszulSlotOut k σ M xs 0 t) := by
  let K := koszulList k σ xs M
  let φ : K ⟶ K := (MvPolynomial.X x : VariableRing k σ) • 𝟙 K
  change koszulSlotIn k σ M xs 0 s ≫ homotopyCofiber.inlX φ 0 1 (natDownStep 0) ≫
    (homotopyCofiber φ).d 1 0 ≫ homotopyCofiber.sndX φ 0 ≫ koszulSlotOut k σ M xs 0 t = _
  erw [homotopyCofiber.d_sndX_assoc φ 1 0 (natDownStep 0)]
  simp only [Preadditive.comp_add,Preadditive.add_comp,Category.assoc,
    homotopyCofiber.inlX_fstX_assoc,homotopyCofiber.inlX_sndX_assoc,zero_comp,add_zero]
  simp [φ]

theorem koszulSlot_d_tail_zero (x : σ) (xs : List σ)
    (s : KoszulSlot xs.length 1) (t : KoszulSlot xs.length 0) :
    koszulSlotIn k σ M (x::xs) 1 (.inr s) ≫ (koszulList k σ (x::xs) M).d 1 0 ≫
      koszulSlotOut k σ M (x::xs) 0 t =
    koszulSlotIn k σ M xs 1 s ≫ (koszulList k σ xs M).d 1 0 ≫ koszulSlotOut k σ M xs 0 t := by
  simp only [koszulSlotIn,koszulSlotOut,Category.assoc]
  erw [homotopyCofiber.inrX_d_assoc]
  simp only [homotopyCofiber.inrX_sndX_assoc]
end NSP14.Homological
