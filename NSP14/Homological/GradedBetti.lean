module

public import NSP14.Homological.GradedKoszulHomology
public import Mathlib.LinearAlgebra.DirectSum.Finite

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits
open scoped DirectSum

namespace NSP14.Homological

universe u
variable (k : Type u) [Field k]

/-- Finite total dimension forces finite degree support; this uses no chain-dimension bound. -/
theorem finiteDirectSumDimensions (A : ℤ → ModuleCat.{u} k)
    [Module.Finite k (⨁ t,A t)] :
    ∃ s : Finset ℤ, (∀ t∉s,Subsingleton (A t)) ∧
      Module.finrank k (⨁ t,A t)=∑ t∈s,Module.finrank k (A t) := by
  classical
  let B := fun t => Module.Free.chooseBasis k (A t)
  have hfin : Module.Finite k (Π₀ t : ℤ,A t) := by
    change Module.Finite k (⨁ t,A t)
    infer_instance
  let : Module.Finite k (Π₀ t : ℤ,A t) := hfin
  let b := DFinsupp.basis B
  let I := Σ t : ℤ, Module.Free.ChooseBasisIndex k (A t)
  let : Finite I := Module.Finite.finite_basis b
  let : Fintype I := Fintype.ofFinite I
  let s : Finset ℤ := Finset.univ.image (fun x : I => x.1)
  have hm (x : I) : x.1∈s := Finset.mem_image.mpr ⟨x,Finset.mem_univ _,rfl⟩
  have hf (t : ℤ) : Module.Finite k (A t) := by
    apply Module.Finite.of_injective (DirectSum.lof k ℤ (fun t => A t) t)
    intro a c he
    simpa using congrArg (fun z => z t) he
  let : ∀ t, Module.Finite k (A t) := hf
  refine ⟨s,?_,?_⟩
  · intro t ht
    let : IsEmpty (Module.Free.ChooseBasisIndex k (A t)) := ⟨fun x => ht (hm ⟨t,x⟩)⟩
    exact ⟨fun a c => (B t).repr.injective (Subsingleton.elim _ _)⟩
  · let e : I ≃ (Σ t : s,Module.Free.ChooseBasisIndex k (A t.val)) := {
      toFun x := ⟨⟨x.1,hm x⟩,x.2⟩
      invFun x := ⟨x.1.val,x.2⟩
      left_inv _ := rfl
      right_inv _ := rfl }
    change Module.finrank k (Π₀ t : ℤ,A t)=_
    rw [Module.finrank_eq_card_basis b,Fintype.card_congr e,Fintype.card_sigma]
    simp only [← Module.finrank_eq_card_basis (B _)]
    exact Finset.sum_coe_sort s (fun t => Module.finrank k (A t))

variable (σ : Type u) [Fintype σ]
variable (M : ModuleCat.{u} (VariableRing k σ)) [Module.Finite (VariableRing k σ) M]
variable (G : GradedPolynomialModule k σ M)

noncomputable def gradedBetti (i : ℕ) (t : ℤ) : ℕ :=
  Module.finrank k ((gradedKoszulComplex k σ M G (variableList k σ) t).homology i)

/-- The internal-degree summands split ordinary derived Tor, via the proved resolution comparison. -/
noncomputable def ordinaryTorGradedSumIso (i : ℕ) :
    (ModuleCat.restrictScalars (algebraMap k (VariableRing k σ))).obj
      (((CategoryTheory.Tor (ModuleCat (VariableRing k σ)) i).obj M).obj (residueField k σ)) ≅
        ModuleCat.of k (⨁ t : ℤ,(gradedKoszulComplex k σ M G (variableList k σ) t).homology i) :=
  torCoefficientIso k σ M i ≪≫ (coefficientKoszulHomologyIso k σ M i).symm ≪≫
    gradedKoszulHomologySumIso k σ M G (variableList k σ) i

noncomputable instance gradedHomologyFinite (i : ℕ) (t : ℤ) :
    Module.Finite k ((gradedKoszulComplex k σ M G (variableList k σ) t).homology i) := by
  let : Module.Finite k ((((ModuleCat.restrictScalars (algebraMap k (VariableRing k σ))).mapHomologicalComplex _).obj
      (koszulList k σ (variableList k σ) M)).homology i) := by
    change Module.Finite k ((coefficientKoszulComplex k σ M).homology i)
    infer_instance
  let e := gradedKoszulHomologySumIso k σ M G (variableList k σ) i
  let : Module.Finite k (⨁ t : ℤ,(gradedKoszulComplex k σ M G (variableList k σ) t).homology i) :=
    Module.Finite.equiv e.toLinearEquiv
  apply Module.Finite.of_injective (DirectSum.lof k ℤ _ t)
  intro a b he
  simpa using congrArg (fun z => z t) he

/-- Finite support and total=finite sum of the actual internal-degree Betti numbers. -/
theorem gradedBetti_total (i : ℕ) :
    ∃ s : Finset ℤ, (∀ t∉s,IsZero ((gradedKoszulComplex k σ M G (variableList k σ) t).homology i)) ∧
      totalBetti k σ M i=∑ t∈s,gradedBetti k σ M G i t := by
  let : Module.Finite k ((((ModuleCat.restrictScalars (algebraMap k (VariableRing k σ))).mapHomologicalComplex _).obj
      (koszulList k σ (variableList k σ) M)).homology i) := by
    change Module.Finite k ((coefficientKoszulComplex k σ M).homology i)
    infer_instance
  let e := gradedKoszulHomologySumIso k σ M G (variableList k σ) i
  let : Module.Finite k (⨁ t : ℤ,(gradedKoszulComplex k σ M G (variableList k σ) t).homology i) :=
    Module.Finite.equiv e.toLinearEquiv
  obtain ⟨s,hs,hd⟩ := finiteDirectSumDimensions k
    (fun t => (gradedKoszulComplex k σ M G (variableList k σ) t).homology i)
  refine ⟨s,fun t ht => ?_,?_⟩
  · let := hs t ht
    exact ModuleCat.isZero_of_subsingleton _
  · change Module.finrank k (koszulHomologyK k σ M i)=_
    have he := e.toLinearEquiv.finrank_eq
    change Module.finrank k ((coefficientKoszulComplex k σ M).homology i)=_ at he
    rw [← (coefficientKoszulHomologyIso k σ M i).toLinearEquiv.finrank_eq,he]
    exact hd

theorem gradedBetti_eq_zero_of_gt (i : ℕ) (hi : Fintype.card σ < i) (t : ℤ) :
    gradedBetti k σ M G i t=0 := by
  classical
  obtain ⟨s,hs,he⟩ := gradedBetti_total k σ M G i
  rw [totalBetti_eq_zero_of_gt k σ M i hi] at he
  by_cases ht : t∈s
  · have hle := Finset.single_le_sum (fun q (_ : q∈s) => Nat.zero_le (gradedBetti k σ M G i q)) ht
    omega
  · let : Subsingleton ((gradedKoszulComplex k σ M G (variableList k σ) t).homology i) :=
      ModuleCat.subsingleton_of_isZero (hs t ht)
    exact Module.finrank_zero_of_subsingleton

end NSP14.Homological
