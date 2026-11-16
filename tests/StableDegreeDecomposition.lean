module
public import NSP14.Lex.StableDegreeDecomposition
@[expose] public section
namespace NSP14.Tests.StableDegreeDecomposition
variable (k : Type) [Field k] (q d : ℕ)
noncomputable def actual_degree_bijection (I : Ideal (MvPolynomial (Fin q) k))
    (hI : Lex.IsStronglyStable k q I) :
    Lex.MinimalDegreeMonomial k q I (d+1) ⊕ Lex.AdjoinDegreeIndex k q I d ≃ Lex.IdealDegreeMonomial k q I (d+1) :=
  Lex.degreeDecompositionEquiv k q I hI d
end NSP14.Tests.StableDegreeDecomposition
