module
public import NSP14.Homological.IdealScalarQuotient
public import NSP14.Homological.KoszulZeroAction
public import NSP14.Homological.KoszulChainDimension
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits HomologicalComplex
namespace NSP14.Homological
universe u
variable (k σ : Type u) [Field k]

noncomputable def variableQuotientModule (xs : List σ) : ModuleCat.{u} (VariableRing k σ) :=
  ModuleCat.of (VariableRing k σ) ((VariableRing k σ) ⧸ variablesIdeal k σ xs)

theorem variableQuotient_regular (xs : List σ) (x : σ) (hx : x ∉ xs) :
    Function.Injective (fun a : variableQuotientModule k σ xs => (MvPolynomial.X x : VariableRing k σ) • a) := by
  change Function.Injective (fun a : (VariableRing k σ) ⧸ variablesIdeal k σ xs =>
    (MvPolynomial.X x : VariableRing k σ) • a)
  let : (variablesIdeal k σ xs).IsPrime := MvPolynomial.span_X_image_isPrime _
  have hn : (Ideal.Quotient.mk (variablesIdeal k σ xs)) (MvPolynomial.X x) ≠ 0 := by
    intro hz
    exact variable_not_mem_variablesIdeal k σ xs x hx (Ideal.Quotient.eq_zero_iff_mem.mp hz)
  intro a b hab
  change (Ideal.Quotient.mk (variablesIdeal k σ xs)) (MvPolynomial.X x)*a=
    (Ideal.Quotient.mk (variablesIdeal k σ xs)) (MvPolynomial.X x)*b at hab
  exact mul_left_cancel₀ hn hab

noncomputable def variableQuotientScalarIso (xs : List σ) (x : σ) :
    scalarModuleQuotient (VariableRing k σ) (MvPolynomial.X x) (variableQuotientModule k σ xs) ≅
      variableQuotientModule k σ (x::xs) :=
  idealScalarQuotientIso (VariableRing k σ) (variablesIdeal k σ xs) (MvPolynomial.X x) ≪≫
    (Submodule.quotEquivOfEq _ _ (by rw [variablesIdeal_cons,sup_comm])).toModuleIso

/-- Remove the live variables by their proved regular action on each
successive actual quotient. The remaining list is left untouched. -/
noncomputable def removeVariableListHomologyIso (C live tail : List σ)
    (hn : live.Nodup) (hd : ∀ x ∈ live,x ∉ C) (i : ℕ) :
    (actionCoefficientComplex k (VariableRing k σ)
      ((live++tail).map (fun x => MvPolynomial.X x)) (variableQuotientModule k σ C)).homology i ≅
    (actionCoefficientComplex k (VariableRing k σ)
      (tail.map (fun x => MvPolynomial.X x)) (variableQuotientModule k σ (live.reverse++C))).homology i := by
  induction live generalizing C with
  | nil => exact Iso.refl _
  | cons x xs ih =>
    have hdis : ∀ y ∈ xs,y ∉ x::C := by
      intro y hy hc
      rcases List.mem_cons.mp hc with he|he
      · subst y
        exact (List.nodup_cons.mp hn).1 hy
      · exact hd y (List.mem_cons_of_mem x hy) he
    let e1 := regularModuleCoefficientReductionIso (VariableRing k σ) (MvPolynomial.X x)
      (variableQuotientModule k σ C) k ((xs++tail).map (fun y => MvPolynomial.X y))
      (variableQuotient_regular k σ C x (hd x (List.mem_cons_self))) i
    let e2 := (homologyFunctor _ (ComplexShape.down ℕ) i).mapIso
      ((actionCoefficientFunctor (VariableRing k σ) k ((xs++tail).map (fun y => MvPolynomial.X y))).mapIso
        (variableQuotientScalarIso k σ C x))
    let e3 := ih (x::C) (List.nodup_cons.mp hn).2 hdis
    exact e1 ≪≫ e2 ≪≫ e3 ≪≫ eqToIso (by simp only [List.reverse_cons,List.append_assoc,List.singleton_append])

variable [Fintype σ]

noncomputable def fullVariableQuotientIso (xs : List σ) (hall : ∀ x,x ∈ xs) :
    variableQuotientModule k σ xs ≅ residueField k σ := by
  have hs : Function.Surjective (augmentationLinear k σ) := by
    intro a
    exact ⟨MvPolynomial.C (show k from a),(augmentation k σ).commutes a⟩
  exact ((Submodule.quotEquivOfEq _ _ (variablesIdeal_fullList_eq_ker k σ xs hall)).trans
    (LinearMap.quotKerEquivOfSurjective (augmentationLinear k σ) hs)).toModuleIso

end NSP14.Homological
