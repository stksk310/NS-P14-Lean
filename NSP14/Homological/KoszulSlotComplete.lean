module
public import NSP14.Homological.KoszulSlotMaps
public import NSP14.Homological.ArrowCone
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped Classical
namespace NSP14.Homological
universe u
variable (k σ : Type u) [Field k] (M : ModuleCat.{u} (VariableRing k σ))

theorem koszulSlotOut_zero (xs : List σ) (j : ℕ) (a : (koszulList k σ xs M).X j)
    (ha : ∀ s,koszulSlotOut k σ M xs j s a=0) : a=0 := by
  induction xs generalizing j with
  | nil => cases j with
    | zero => exact ha PUnit.unit
    | succ j =>
      have : Subsingleton ((koszulList k σ [] M).X (j+1)) :=
        ModuleCat.subsingleton_of_isZero (koszul_piece_isZero_of_gt k σ [] M (j+1) (by simp))
      exact Subsingleton.elim _ _
  | cons x xs ih =>
    cases j with
    | zero =>
      apply (scalarConeZeroIso (VariableRing k σ) (MvPolynomial.X x) (koszulList k σ xs M)).toLinearEquiv.injective
      change homotopyCofiber.sndX ((MvPolynomial.X x : VariableRing k σ) • 𝟙 (koszulList k σ xs M)) 0 a=
        homotopyCofiber.sndX ((MvPolynomial.X x : VariableRing k σ) • 𝟙 (koszulList k σ xs M)) 0 0
      rw [map_zero]
      apply ih 0
      intro s
      exact ha s
    | succ j =>
      have hf : homotopyCofiber.fstX ((MvPolynomial.X x : VariableRing k σ) • 𝟙 (koszulList k σ xs M))
          (j+1) j (natDownStep j) a=0 := by
        apply ih j
        intro s
        exact ha (.inl s)
      have hs : homotopyCofiber.sndX ((MvPolynomial.X x : VariableRing k σ) • 𝟙 (koszulList k σ xs M)) (j+1) a=0 := by
        apply ih (j+1)
        intro s
        exact ha (.inr s)
      rw [arrowCone_split (VariableRing k σ) _ j a,hf,hs,map_zero,map_zero,zero_add]

/-- Every actual chain is the sum of its polynomial-linear split slots. -/
theorem koszulSlot_decompose (xs : List σ) (j : ℕ) (a : (koszulList k σ xs M).X j) :
    a=∑ s,koszulSlotIn k σ M xs j s (koszulSlotOut k σ M xs j s a) := by
  have hz : a-∑ s,koszulSlotIn k σ M xs j s (koszulSlotOut k σ M xs j s a)=0 := by
    apply koszulSlotOut_zero k σ M xs j
    intro t
    rw [map_sub,map_sum]
    have he (s : KoszulSlot xs.length j) :
        koszulSlotOut k σ M xs j t (koszulSlotIn k σ M xs j s (koszulSlotOut k σ M xs j s a))=
          if s=t then koszulSlotOut k σ M xs j s a else 0 := by
      have h := congrArg (fun f => f (koszulSlotOut k σ M xs j s a)) (koszulSlotIn_Out k σ M xs j s t)
      by_cases he : s=t
      · subst t
        simpa only [ite_true,ModuleCat.comp_apply,ModuleCat.id_apply] using h
      · simpa only [he,ite_false,ModuleCat.comp_apply,ModuleCat.hom_zero,LinearMap.zero_apply] using h
    simp only [he]
    simp
  exact sub_eq_zero.mp hz
end NSP14.Homological
