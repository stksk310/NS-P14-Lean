module
public import NSP14
@[expose] public section
namespace CutBasisAcceptance
open NSP14
variable {S : NumericalSemigroup} {k : Type} [Field k] (C : S.LinearCutData k)
theorem keep_literal_cut (i : Fin S.actualCutRank) :
    C.extendedPolynomialEquiv (MvPolynomial.X (Fin.castAdd C.complementRank i))=C.polynomialForm i :=
  C.extendedPolynomialEquiv_prefix i
end CutBasisAcceptance
