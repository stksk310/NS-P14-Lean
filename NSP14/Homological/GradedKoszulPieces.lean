module
public import NSP14.Homological.GradedKoszulSplit
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits HomologicalComplex
namespace NSP14.Homological
universe u
variable (k σ : Type u) [Field k]
  (M : ModuleCat.{u} (VariableRing k σ)) (G : GradedPolynomialModule k σ M)

noncomputable def gradedKoszulSpaceEquiv (xs : List σ) (t : ℤ) (i : ℕ) :
    (koszulChainGrading k σ M G xs i).piece (t-(i:ℤ)) ≃ₗ[k] gradedKoszulSpace k σ M G xs t i :=
  (koszulChainGrading k σ M G xs i).rangeEquiv (t-(i:ℤ))

theorem koszulChainGrading_zero_piece (xs : List σ) (q : ℤ) :
    (koszulChainGrading k σ M G xs 0).piece q=G.piece q := by
  induction xs with
  | nil => rfl
  | cons x xs ih => exact ih

theorem koszulChainGrading_piece_subsingleton (xs : List σ) (q : ℤ)
    (hG : Subsingleton (G.piece q)) (i : ℕ) :
    Subsingleton ((koszulChainGrading k σ M G xs i).piece q) := by
  induction xs generalizing i with
  | nil =>
    cases i with
    | zero => exact hG
    | succ i => change Subsingleton PUnit; infer_instance
  | cons x xs ih =>
    cases i with
    | zero => exact ih 0
    | succ i =>
      let : Subsingleton ((koszulChainGrading k σ M G xs i).piece q) := ih i
      let : Subsingleton ((koszulChainGrading k σ M G xs (i+1)).piece q) := ih (i+1)
      change Subsingleton (((koszulChainGrading k σ M G xs i).piece q) ×
        ((koszulChainGrading k σ M G xs (i+1)).piece q))
      infer_instance

theorem gradedKoszulSpace_subsingleton (xs : List σ) (t : ℤ) (i : ℕ)
    (hG : Subsingleton (G.piece (t-(i:ℤ)))) : Subsingleton (gradedKoszulSpace k σ M G xs t i) := by
  let : Subsingleton ((koszulChainGrading k σ M G xs i).piece (t-(i:ℤ))) :=
    koszulChainGrading_piece_subsingleton k σ M G xs (t-(i:ℤ)) hG i
  let e := gradedKoszulSpaceEquiv k σ M G xs t i
  exact ⟨fun a b => e.symm.injective (Subsingleton.elim _ _)⟩

theorem gradedKoszulSpace_zero_finrank (xs : List σ) (t : ℤ) :
    Module.finrank k (gradedKoszulSpace k σ M G xs t 0)=Module.finrank k (G.piece t) := by
  have h := (gradedKoszulSpaceEquiv k σ M G xs t 0).finrank_eq
  change Module.finrank k ((koszulChainGrading k σ M G xs 0).piece (t-(0:ℤ)))=
    Module.finrank k (gradedKoszulSpace k σ M G xs t 0) at h
  rw [sub_zero,koszulChainGrading_zero_piece] at h
  exact h.symm

variable [Fintype σ] [Module.Finite (VariableRing k σ) M]

theorem gradedBetti_le_total (i : ℕ) (t : ℤ) : gradedBetti k σ M G i t ≤ totalBetti k σ M i := by
  obtain ⟨s,hs,he⟩ := gradedBetti_total k σ M G i
  by_cases ht : t ∈ s
  · rw [he]
    exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) ht
  · let : Subsingleton ((gradedKoszulComplex k σ M G (variableList k σ) t).homology i) :=
      ModuleCat.subsingleton_of_isZero (hs t ht)
    have hz : gradedBetti k σ M G i t=0 := Module.finrank_zero_of_subsingleton
    rw [hz]
    exact Nat.zero_le _

end NSP14.Homological
