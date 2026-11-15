module
public import NSP14.Lex.StrongStableEK
@[expose] public section
open scoped Classical BigOperators
attribute [local instance] MvPolynomial.gradedAlgebra
namespace NSP14.Tests.StrongStableEK
variable (k : Type) [Field k] (q : ℕ)

theorem actual_stable_graded_ek (I : Ideal (MvPolynomial (Fin q) k))
    (hI : Lex.IsStronglyStable k q I) (hproper : I≠⊤)
    (hHom : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin q) k))
    (g : Finset (Fin q →₀ ℕ)) (hg : ∀ v,v∈g ↔ Lex.MinimalGenerator k q I v)
    (i : ℕ) (hi : 1 ≤ i) (t : ℤ) :
    Lex.quotientGradedBetti k q I hHom i t=
      ∑ v∈g,if (v.degree:ℤ)+(i:ℤ)-1=t then (Lex.maxVariable q v-1).choose (i-1) else 0 :=
  Lex.IsStronglyStable.graded_ek k q hI hproper hHom g hg i hi t
end NSP14.Tests.StrongStableEK
