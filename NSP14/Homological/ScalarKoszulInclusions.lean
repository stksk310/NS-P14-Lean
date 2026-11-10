module

public import NSP14.Homological.GradedScalarComparison
public import NSP14.Homological.KoszulGradedInclusions

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory HomologicalComplex
open scoped TensorProduct

namespace NSP14.Homological

universe u
variable (k L σ : Type u) [Field k] [Field L] [Algebra k L]
variable {M : ModuleCat.{u} (VariableRing k σ)} {N : ModuleCat.{u} (VariableRing L σ)}

/-- Pure-tensor expression of the actual polynomial scalar-extension functor. -/
theorem polynomialBaseChangeFunctor_map_tmul {A B : ModuleCat.{u} (VariableRing k σ)}
    (f : A ⟶ B) (l : L) (a : coefficientModule k σ A) :
    (polynomialBaseChangeFunctor k L σ).map f (l ⊗ₜ[k] a)=
      l ⊗ₜ[k] (coefficientMap k σ f a) := by
  exact LinearMap.baseChange_tmul _ _ _

theorem scalarKoszulPieceIso_inr_tmul (e : polynomialBaseChangeModule k L σ M ≅ N)
    (x : σ) (xs : List σ) (i : ℕ) (l : L)
    (a : coefficientModule k σ ((koszulList k σ xs M).X i)) :
    scalarKoszulPieceIso k L σ e (x::xs) i (l ⊗ₜ[k]
      (show coefficientModule k σ ((koszulList k σ (x::xs) M).X i) from
        homotopyCofiber.inrX ((MvPolynomial.X x : VariableRing k σ) • 𝟙 (koszulList k σ xs M)) i a)) =
      homotopyCofiber.inrX ((MvPolynomial.X x : VariableRing L σ) • 𝟙 (koszulList L σ xs N)) i
        (scalarKoszulPieceIso k L σ e xs i (l ⊗ₜ[k] a)) := by
  have he := congrArg (fun f => f.hom (l ⊗ₜ[k] a)) (polynomialKoszulTotalIso_inr k L σ e x xs i)
  simp only [ModuleCat.hom_comp,LinearMap.comp_apply] at he
  erw [polynomialBaseChangeFunctor_map_tmul] at he
  exact he

theorem scalarKoszulPieceIso_inl_tmul (e : polynomialBaseChangeModule k L σ M ≅ N)
    (x : σ) (xs : List σ) (i : ℕ) (l : L)
    (a : coefficientModule k σ ((koszulList k σ xs M).X i)) :
    scalarKoszulPieceIso k L σ e (x::xs) (i+1) (l ⊗ₜ[k]
      (show coefficientModule k σ ((koszulList k σ (x::xs) M).X (i+1)) from
        homotopyCofiber.inlX ((MvPolynomial.X x : VariableRing k σ) • 𝟙 (koszulList k σ xs M)) i (i+1) (natDownStep i) a)) =
      homotopyCofiber.inlX ((MvPolynomial.X x : VariableRing L σ) • 𝟙 (koszulList L σ xs N)) i (i+1) (natDownStep i)
        (scalarKoszulPieceIso k L σ e xs i (l ⊗ₜ[k] a)) := by
  have he := congrArg (fun f => f.hom (l ⊗ₜ[k] a)) (polynomialKoszulTotalIso_inl k L σ e x xs i)
  simp only [ModuleCat.hom_comp,LinearMap.comp_apply] at he
  erw [polynomialBaseChangeFunctor_map_tmul] at he
  exact he

variable (G : GradedPolynomialModule k σ M) (H : GradedPolynomialModule L σ N)
variable (e : polynomialBaseChangeModule k L σ M ≅ N)

/-- The recursively extended actual degree pieces commute with the SAME total comparison. -/
theorem scalarKoszulGradePieceIso_inclusion (C : GradedScalarComparison k L σ G H e)
    (xs : List σ) (i : ℕ) (q : ℤ) (a : (koszulChainGrading k σ M G xs i).piece q) :
    (koszulChainGrading L σ N H xs i).inclusion q
        (scalarKoszulGradePieceIso k L σ G H e C xs i q ((1:L) ⊗ₜ[k] a)) =
      scalarKoszulPieceIso k L σ e xs i
        ((1:L) ⊗ₜ[k] (koszulChainGrading k σ M G xs i).inclusion q a) := by
  induction xs generalizing i with
  | nil =>
    cases i with
    | zero => exact C.inclusion_commutes q a
    | succ i =>
      let : Subsingleton ((koszulChainGrading k σ M G [] (i+1)).piece q) :=
        (show Subsingleton PUnit from inferInstance)
      have ha : a=0 := Subsingleton.elim _ _
      rw [ha]
      simp only [map_zero,TensorProduct.tmul_zero]
  | cons x xs ih =>
    cases i with
    | zero =>
      change (koszulChainGrading L σ N H (x::xs) 0).inclusion q
        (scalarKoszulGradePieceIso k L σ G H e C xs 0 q ((1:L) ⊗ₜ[k] a)) = _
      rw [koszulChainGrading_inclusion_zero,koszulChainGrading_inclusion_zero,ih,
        scalarKoszulPieceIso_inr_tmul]
    | succ i =>
      rcases a with ⟨a,b⟩
      change (koszulChainGrading L σ N H (x::xs) (i+1)).inclusion q
        (scalarKoszulGradePieceIso k L σ G H e C xs i q ((1:L) ⊗ₜ[k] a),
          scalarKoszulGradePieceIso k L σ G H e C xs (i+1) q ((1:L) ⊗ₜ[k] b)) = _
      rw [koszulChainGrading_inclusion_succ,koszulChainGrading_inclusion_succ,
        TensorProduct.tmul_add,map_add,scalarKoszulPieceIso_inl_tmul,scalarKoszulPieceIso_inr_tmul,
        ih i,ih (i+1)]

end NSP14.Homological
