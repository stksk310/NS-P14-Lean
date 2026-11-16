module

public import NSP14.Homological.KoszulChainDimension
public import NSP14.Homological.KoszulZeroAction
public import NSP14.Homological.KoszulFree

@[expose] public section

open CategoryTheory

namespace NSP14.Homological

universe u
variable (k σ : Type u) [Field k] [Fintype σ]

noncomputable instance residuePolynomialFinite : Module.Finite (VariableRing k σ) (residueField k σ) :=
  Module.Finite.of_surjective (augmentationLinear k σ) (by
    intro a
    exact ⟨MvPolynomial.C (show k from a),(augmentation k σ).commutes a⟩)

noncomputable instance residueCoefficientFinite : Module.Finite k (coefficientModule k σ (residueField k σ)) :=
  Module.Finite.equiv (residueCoefficientIso k σ).symm.toLinearEquiv

/-- The classical binomial Betti numbers of the residue field, from the actual zero differential. -/
theorem residue_totalBetti (i : ℕ) : totalBetti k σ (residueField k σ) i=Nat.choose (Fintype.card σ) i := by
  let e := koszulHomologyZeroActionIso k σ (variableList k σ) (residueField k σ)
    (fun x _ a => residueField_variable k σ x a) i
  have hk := ((ModuleCat.restrictScalars (algebraMap k (VariableRing k σ))).mapIso e).toLinearEquiv.finrank_eq
  change totalBetti k σ (residueField k σ) i =
    Module.finrank k (coefficientModule k σ ((koszulList k σ (variableList k σ) (residueField k σ)).X i)) at hk
  rw [hk,koszul_chain_finrank,variableList_length]
  have he := (residueCoefficientIso k σ).toLinearEquiv.finrank_eq
  change Module.finrank k (coefficientModule k σ (residueField k σ))=Module.finrank k k at he
  rw [he,Module.finrank_self,Nat.one_mul]

end NSP14.Homological
