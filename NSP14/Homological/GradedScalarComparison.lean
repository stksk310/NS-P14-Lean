module

public import NSP14.Homological.GradedBaseChange
public import NSP14.Homological.KoszulScalarComponents
public import Mathlib.LinearAlgebra.TensorProduct.Prod

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory HomologicalComplex
open scoped TensorProduct

namespace NSP14.Homological

universe u
variable (k L σ : Type u) [Field k] [Field L] [Algebra k L]
variable {M : ModuleCat.{u} (VariableRing k σ)} {N : ModuleCat.{u} (VariableRing L σ)}

/-- Degree comparisons for an already specified actual coefficient-change map.
The inclusion condition prevents installing an unrelated transported target grading. -/
structure GradedScalarComparison (G : GradedPolynomialModule k σ M)
    (H : GradedPolynomialModule L σ N) (e : polynomialBaseChangeModule k L σ M ≅ N) where
  pieceIso : ∀ q,(L ⊗[k] G.piece q) ≃ₗ[L] H.piece q
  inclusion_commutes : ∀ q (a : G.piece q),
    H.inclusion q (pieceIso q ((1:L) ⊗ₜ[k] a)) =
      e.hom ((1:L) ⊗ₜ[k] G.inclusion q a)

noncomputable def scalarKoszulPieceIso
    (e : polynomialBaseChangeModule k L σ M ≅ N) (xs : List σ) (i : ℕ) :
    (L ⊗[k] coefficientModule k σ ((koszulList k σ xs M).X i)) ≃ₗ[L]
      coefficientModule L σ ((koszulList L σ xs N).X i) :=
  (polynomialBaseChangeCoefficientIso k L σ ((koszulList k σ xs M).X i)).symm.toLinearEquiv.trans
    (((ModuleCat.restrictScalars (algebraMap L (VariableRing L σ))).mapIso
      ((HomologicalComplex.eval _ (ComplexShape.down ℕ) i).mapIso
        (polynomialKoszulTotalIso k L σ e xs))).toLinearEquiv)

/-- The coefficient comparison is the literal component of the total comparison. -/
theorem scalarKoszulPieceIso_apply
    (e : polynomialBaseChangeModule k L σ M ≅ N) (xs : List σ) (i : ℕ)
    (a : L ⊗[k] coefficientModule k σ ((koszulList k σ xs M).X i)) :
    scalarKoszulPieceIso k L σ e xs i a=(polynomialKoszulTotalIso k L σ e xs).hom.f i a := rfl

variable (G : GradedPolynomialModule k σ M) (H : GradedPolynomialModule L σ N)
variable (e : polynomialBaseChangeModule k L σ M ≅ N)

/-- Scalar extension on coefficient-degree pieces, with the same recursive exterior blocks. -/
noncomputable def scalarKoszulGradePieceIso (C : GradedScalarComparison k L σ G H e) :
    ∀ (xs : List σ) (i : ℕ) (q : ℤ),
      (L ⊗[k] (koszulChainGrading k σ M G xs i).piece q) ≃ₗ[L]
        (koszulChainGrading L σ N H xs i).piece q
  | [],0,q => C.pieceIso q
  | [],i+1,q => by
      let : Subsingleton ((koszulChainGrading k σ M G [] (i+1)).piece q) :=
        (show Subsingleton PUnit from inferInstance)
      let : Subsingleton ((koszulChainGrading L σ N H [] (i+1)).piece q) :=
        (show Subsingleton PUnit from inferInstance)
      exact LinearEquiv.ofSubsingleton _ _
  | x::xs,0,q => scalarKoszulGradePieceIso C xs 0 q
  | x::xs,i+1,q => (TensorProduct.prodRight k L L _ _).trans
      ((scalarKoszulGradePieceIso C xs i q).prodCongr (scalarKoszulGradePieceIso C xs (i+1) q))

end NSP14.Homological
