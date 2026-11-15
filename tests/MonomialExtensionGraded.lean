module
public import NSP14.Lex.MonomialExtensionGraded
@[expose] public section
attribute [local instance] MvPolynomial.gradedAlgebra
namespace NSP14.Tests.MonomialExtensionGraded
theorem actual_map_homogeneous (k L : Type) [Field k] [Field L] [Algebra k L] (q : ℕ)
    (I : Ideal (MvPolynomial (Fin q) k)) (hmono : Lex.IsMonomial k q I) :
    (I.map (MvPolynomial.map (algebraMap k L))).IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin q) L) :=
  Lex.monomialMap_homogeneous k L q I hmono

theorem actual_map_all_graded_betti (k L : Type) [Field k] [Field L] [Algebra k L] (q : ℕ)
    (I : Ideal (MvPolynomial (Fin q) k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin q) k))
    (hmono : Lex.IsMonomial k q I)
    (hMap : (I.map (MvPolynomial.map (algebraMap k L))).IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin q) L)) (i : ℕ) (t : ℤ) :
    Lex.quotientGradedBetti L q (I.map (MvPolynomial.map (algebraMap k L))) hMap i t=
      Lex.quotientGradedBetti k q I hI i t :=
  Lex.monomialMap_gradedBetti k L q I hI hmono i t
end NSP14.Tests.MonomialExtensionGraded
