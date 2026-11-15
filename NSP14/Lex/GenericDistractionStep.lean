module
public import NSP14.Lex.MonomialExtensionGraded
public import NSP14.Lex.InitialBetti
@[expose] public section
open scoped Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] MvPolynomial.gradedAlgebra
namespace NSP14.Lex
variable (k : Type) [Field k] (q : ℕ)
local notation "K" => GenericDistractionField k q

/-- One actual generic-distraction/initial-ideal operation. Lexness is not asserted. -/
def genericMonomialStep (I : Ideal (MvPolynomial (Fin q) k)) : Ideal (MvPolynomial (Fin q) K) :=
  initialIdeal K q MonomialOrder.degLex
    (genericDistractionIdeal k q (monomialExtension k K q I))

theorem genericMonomialStep_homogeneous (I : Ideal (MvPolynomial (Fin q) k)) :
    (genericMonomialStep k q I).IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin q) K) :=
  initialIdeal_homogeneous K q MonomialOrder.degLex _

theorem genericMonomialStep_isMonomial (I : Ideal (MvPolynomial (Fin q) k)) :
    IsMonomial K q (genericMonomialStep k q I) := initialIdeal_isMonomial K q MonomialOrder.degLex _

theorem genericMonomialStep_sameHilbert (I : Ideal (MvPolynomial (Fin q) k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin q) k))
    (hmono : IsMonomial k q I) (n : ℕ) :
    quotientHilbert k q I hI n=quotientHilbert K q (genericMonomialStep k q I)
      (genericMonomialStep_homogeneous k q I) n :=
  (monomialExtension_sameHilbert k K q I hI hmono n).trans
    ((genericDistraction_sameHilbert k q (monomialExtension k K q I)
      (monomialExtension_homogeneous k K q I) (monomialExtension_isMonomial k K q I) n).trans
      (initialIdeal_sameHilbert K q _ (genericDistractionIdeal_homogeneous k q _) n))

theorem genericMonomialStep_gradedBetti_le (I : Ideal (MvPolynomial (Fin q) k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin q) k))
    (hmono : IsMonomial k q I) (i : ℕ) (t : ℤ) :
    quotientGradedBetti k q I hI i t≤quotientGradedBetti K q (genericMonomialStep k q I)
      (genericMonomialStep_homogeneous k q I) i t := by
  rw [← genericDistraction_original_gradedBetti k q I hI hmono i t]
  exact quotientGradedBetti_initial_le K q _ (genericDistractionIdeal_homogeneous k q _) i t

def genericHomogeneousStep (I : Ideal (MvPolynomial (Fin q) k)) : Ideal (MvPolynomial (Fin q) K) :=
  genericMonomialStep k q (initialIdeal k q MonomialOrder.degLex I)

theorem genericHomogeneousStep_homogeneous (I : Ideal (MvPolynomial (Fin q) k)) :
    (genericHomogeneousStep k q I).IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin q) K) :=
  genericMonomialStep_homogeneous k q _

theorem genericHomogeneousStep_isMonomial (I : Ideal (MvPolynomial (Fin q) k)) :
    IsMonomial K q (genericHomogeneousStep k q I) := genericMonomialStep_isMonomial k q _

theorem genericHomogeneousStep_sameHilbert (I : Ideal (MvPolynomial (Fin q) k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin q) k)) (n : ℕ) :
    quotientHilbert k q I hI n=quotientHilbert K q (genericHomogeneousStep k q I)
      (genericHomogeneousStep_homogeneous k q I) n :=
  (initialIdeal_sameHilbert k q I hI n).trans (genericMonomialStep_sameHilbert k q _
    (initialIdeal_homogeneous k q MonomialOrder.degLex I)
    (initialIdeal_isMonomial k q MonomialOrder.degLex I) n)

theorem genericHomogeneousStep_gradedBetti_le (I : Ideal (MvPolynomial (Fin q) k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin q) k)) (i : ℕ) (t : ℤ) :
    quotientGradedBetti k q I hI i t≤quotientGradedBetti K q (genericHomogeneousStep k q I)
      (genericHomogeneousStep_homogeneous k q I) i t :=
  (quotientGradedBetti_initial_le k q I hI i t).trans
    (genericMonomialStep_gradedBetti_le k q _ (initialIdeal_homogeneous k q MonomialOrder.degLex I)
      (initialIdeal_isMonomial k q MonomialOrder.degLex I) i t)
end NSP14.Lex
