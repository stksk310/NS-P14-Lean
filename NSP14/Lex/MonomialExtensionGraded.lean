module
public import NSP14.Lex.MonomialExtension
public import NSP14.Homological.BasisGradedScalarComparison
public import NSP14.Homological.GradedScalarKoszul
public import NSP14.Lex.DistractionGraded
@[expose] public section
open scoped Classical TensorProduct
open CategoryTheory NSP14.Homological
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] MvPolynomial.gradedAlgebra

namespace NSP14.Lex
variable (k L : Type) [Field k] [Field L] [Algebra k L] (q : ℕ)

def monomialExtensionGradedComparison (I : Ideal (MvPolynomial (Fin q) k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin q) k))
    (hmono : IsMonomial k q I) :
    GradedScalarComparison k L (Fin q)
      (Endpoint.artinGrading k (Fin q) I hI)
      (Endpoint.artinGrading L (Fin q) (monomialExtension k L q I) (monomialExtension_homogeneous k L q I))
      (monomialExtensionBaseChangeIso k L q I hmono) :=
  basisGradedScalarComparison k L (Fin q)
    (Endpoint.artinModule k (Fin q) I) (Endpoint.artinModule L (Fin q) (monomialExtension k L q I))
    (Endpoint.artinGrading k (Fin q) I hI)
    (Endpoint.artinGrading L (Fin q) (monomialExtension k L q I) (monomialExtension_homogeneous k L q I))
    (Endpoint.artinMonomialBasis k q I) (monomialExtensionBasis k L q I hmono)
    (fun p => (p.val.degree:ℤ)) (Endpoint.artinMonomialBasis_homogeneous k q I hI)
    (monomialExtensionBasis_homogeneous k L q I hmono) (monomialExtensionBaseChangeIso k L q I hmono)
    (monomialExtensionBaseChangeIso_basis k L q I hmono)

theorem monomialExtension_gradedBetti (I : Ideal (MvPolynomial (Fin q) k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin q) k))
    (hmono : IsMonomial k q I) (i : ℕ) (t : ℤ) :
    quotientGradedBetti L q (monomialExtension k L q I) (monomialExtension_homogeneous k L q I) i t=
      quotientGradedBetti k q I hI i t :=
  gradedScalarBetti_baseChange k L (Fin q) (Endpoint.artinGrading k (Fin q) I hI)
    (Endpoint.artinGrading L (Fin q) (monomialExtension k L q I) (monomialExtension_homogeneous k L q I))
    (monomialExtensionBaseChangeIso k L q I hmono) (monomialExtensionGradedComparison k L q I hI hmono) i t

theorem monomialMap_homogeneous (I : Ideal (MvPolynomial (Fin q) k)) (hmono : IsMonomial k q I) :
    (I.map (MvPolynomial.map (algebraMap k L))).IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin q) L) := by
  rw [← monomialExtension_eq_map k L q I hmono]
  exact monomialExtension_homogeneous k L q I

theorem monomialMap_gradedBetti (I : Ideal (MvPolynomial (Fin q) k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin q) k))
    (hmono : IsMonomial k q I) (i : ℕ) (t : ℤ) :
    quotientGradedBetti L q (I.map (MvPolynomial.map (algebraMap k L)))
      (monomialMap_homogeneous k L q I hmono) i t = quotientGradedBetti k q I hI i t :=
  (Endpoint.artinGradedBetti_congr L (Fin q) (monomialExtension k L q I)
    (I.map (MvPolynomial.map (algebraMap k L)))
    (monomialExtension_homogeneous k L q I) (monomialMap_homogeneous k L q I hmono)
    (monomialExtension_eq_map k L q I hmono) i t).symm.trans
      (monomialExtension_gradedBetti k L q I hI hmono i t)
end NSP14.Lex

namespace NSP14.Lex
variable (k : Type) [Field k] (q : ℕ)
local notation "K" => GenericDistractionField k q

theorem genericDistraction_original_gradedBetti (I : Ideal (MvPolynomial (Fin q) k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin q) k))
    (hmono : IsMonomial k q I) (i : ℕ) (t : ℤ) :
    quotientGradedBetti K q (genericDistractionIdeal k q (monomialExtension k K q I))
      (genericDistractionIdeal_homogeneous k q (monomialExtension k K q I)) i t=
      quotientGradedBetti k q I hI i t :=
  (genericDistraction_gradedBetti k q (monomialExtension k K q I)
    (monomialExtension_homogeneous k K q I) (monomialExtension_isMonomial k K q I) i t).symm.trans
      (monomialExtension_gradedBetti k K q I hI hmono i t)
end NSP14.Lex
