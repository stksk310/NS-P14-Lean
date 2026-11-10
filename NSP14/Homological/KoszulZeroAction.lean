module

public import NSP14.Homological.KoszulLongExact

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace NSP14.Homological

universe u
variable (k σ : Type u) [Field k]

theorem koszul_chain_scalar_annihilates (xs : List σ) (M : ModuleCat.{u} (VariableRing k σ))
    (r : VariableRing k σ) (hr : ∀ m : M,r • m=0) (i : ℕ) (a : (koszulList k σ xs M).X i) : r • a=0 := by
  induction xs generalizing i with
  | nil =>
    cases i with
    | zero => exact hr a
    | succ i =>
      have : Subsingleton ((koszulList k σ [] M).X (i+1)) := ModuleCat.subsingleton_of_isZero
        (koszul_piece_isZero_of_gt k σ [] M (i+1) (by simp))
      exact Subsingleton.elim _ _
  | cons x xs ih =>
    cases i with
    | zero =>
      apply (koszulZeroIso k σ (x::xs) M).toLinearEquiv.injective
      change (koszulZeroIso k σ (x::xs) M).hom.hom (r • a)=(koszulZeroIso k σ (x::xs) M).hom.hom 0
      rw [map_smul,hr,map_zero]
    | succ i =>
      apply cone_element_ext (koszulList k σ xs M) (MvPolynomial.X x) i
      · change coneFirst _ _ _ (r • a)=coneFirst _ _ _ 0
        rw [map_smul,ih,map_zero]
      · change coneSecond _ _ _ (r • a)=coneSecond _ _ _ 0
        rw [map_smul,ih,map_zero]

/-- When all listed variables act by zero, the actual signed differential is zero. -/
theorem koszul_d_eq_zero_of_zero_action (xs : List σ) (M : ModuleCat.{u} (VariableRing k σ))
    (hx : ∀ x∈xs, ∀ m : M,(MvPolynomial.X x : VariableRing k σ) • m=0) :
    ∀ i j,(koszulList k σ xs M).d i j=0 := by
  induction xs with
  | nil => intro i j; apply HomologicalComplex.single_obj_d
  | cons x xs ih =>
    have hold := ih (fun y hy => hx y (List.mem_cons_of_mem x hy))
    intro i j
    by_cases hij : (ComplexShape.down ℕ).Rel i j
    · have he : j+1=i := hij
      subst i
      apply ModuleCat.hom_ext
      ext a
      cases j with
      | zero =>
        apply (scalarConeZeroIso (VariableRing k σ) (MvPolynomial.X x) (koszulList k σ xs M)).toLinearEquiv.injective
        change coneSecond (koszulList k σ xs M) (MvPolynomial.X x) 0 (_)=coneSecond _ _ 0 0
        erw [cone_d_second,hold]
        change (MvPolynomial.X x : VariableRing k σ) • coneFirst _ _ 0 a+0=0
        rw [koszul_chain_scalar_annihilates k σ xs M _ (hx x (List.mem_cons_self)),add_zero]
      | succ j =>
        apply cone_element_ext (koszulList k σ xs M) (MvPolynomial.X x) j
        · erw [cone_d_first,hold]
          change -(0 : (koszulList k σ xs M).X j)=coneFirst _ _ j 0
          rw [neg_zero,map_zero]
        · erw [cone_d_second,hold]
          rw [koszul_chain_scalar_annihilates k σ xs M _ (hx x (List.mem_cons_self))]
          change 0+0=coneSecond _ _ (j+1) 0
          rw [zero_add,map_zero]
    · exact (koszulList k σ (x::xs) M).shape i j hij

noncomputable def koszulHomologyZeroActionIso (xs : List σ) (M : ModuleCat.{u} (VariableRing k σ))
    (hx : ∀ x∈xs, ∀ m : M,(MvPolynomial.X x : VariableRing k σ) • m=0) (i : ℕ) :
    koszulHomology k σ xs M i ≅ (koszulList k σ xs M).X i :=
  (ShortComplex.HomologyData.ofZeros ((koszulList k σ xs M).sc i)
    (koszul_d_eq_zero_of_zero_action k σ xs M hx _ _)
    (koszul_d_eq_zero_of_zero_action k σ xs M hx _ _)).left.homologyIso

end NSP14.Homological
