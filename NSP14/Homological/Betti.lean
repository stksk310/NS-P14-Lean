module

public import NSP14.Homological.KoszulAnnihilation
public import Mathlib.LinearAlgebra.Dimension.Constructions

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace NSP14.Homological

universe u
variable (k σ : Type u) [Field k] [Fintype σ]

/-- Total Betti is defined only in the finite-generation interface; its k-finiteness is proved. -/
noncomputable def totalBetti (M : ModuleCat.{u} (VariableRing k σ))
    [Module.Finite (VariableRing k σ) M] (i : ℕ) : ℕ :=
  Module.finrank k (koszulHomologyK k σ M i)

theorem totalBetti_eq_zero_of_gt (M : ModuleCat.{u} (VariableRing k σ))
    [Module.Finite (VariableRing k σ) M] (i : ℕ) (hi : Fintype.card σ < i) : totalBetti k σ M i=0 := by
  have hz := koszul_homology_isZero_of_gt k σ (variableList k σ) M i
    (by rwa [variableList_length])
  have : Subsingleton (koszulHomologyK k σ M i) := (show Subsingleton (koszulHomology k σ (variableList k σ) M i) from ModuleCat.subsingleton_of_isZero hz)
  exact Module.finrank_zero_of_subsingleton

/-- Coefficient-linear transport induced by the very same polynomial-module isomorphism. -/
noncomputable def koszulHomologyKIso {M N : ModuleCat.{u} (VariableRing k σ)} (e : M ≅ N) (i : ℕ) :
    koszulHomologyK k σ M i ≅ koszulHomologyK k σ N i := by
  have h := koszulHomologyIso k σ (variableList k σ) i e
  change ((koszulFunctor k σ (variableList k σ)).obj M).homology i ≅
    ((koszulFunctor k σ (variableList k σ)).obj N).homology i at h
  simp only [koszulFunctor_obj] at h
  exact (ModuleCat.restrictScalars (algebraMap k (VariableRing k σ))).mapIso h

theorem totalBetti_iso {M N : ModuleCat.{u} (VariableRing k σ)}
    [Module.Finite (VariableRing k σ) M] [Module.Finite (VariableRing k σ) N]
    (e : M ≅ N) (i : ℕ) : totalBetti k σ M i=totalBetti k σ N i :=
  (koszulHomologyKIso k σ e i).toLinearEquiv.finrank_eq

/-- The total-Betti vector space is the coefficient restriction of ordinary Tor. -/
noncomputable def torCoefficientIso (M : ModuleCat.{u} (VariableRing k σ)) (i : ℕ) :
    (ModuleCat.restrictScalars (algebraMap k (VariableRing k σ))).obj
      (((CategoryTheory.Tor (ModuleCat (VariableRing k σ)) i).obj M).obj (residueField k σ)) ≅
        koszulHomologyK k σ M i :=
  (ModuleCat.restrictScalars (algebraMap k (VariableRing k σ))).mapIso (torKoszulIso k σ M i)

end NSP14.Homological
