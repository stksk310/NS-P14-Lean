module
public import tests.Run13Fixtures
@[expose] public section
namespace Run13Presentation
open NSP14 NSP14.NumericalSemigroup
variable (S : NumericalSemigroup) (k : Type) [Field k]
theorem full_variables : Fintype.card S.AtomExponent=S.embeddingDimension := S.atomExponent_card
theorem nonx_variables : Fintype.card S.NonXAtom=S.embeddingDimension-1 := S.nonXAtom_card
theorem actual_surjection : Function.Surjective (S.fullPolynomialToG k) := S.fullPolynomialToG_surjective k
theorem actual_homogeneous (p : S.FullPolynomialRing k) (n : ℕ) (hp : p.IsHomogeneous n) :
    S.fullPolynomialToG k p∈S.tangentDegree k n := S.fullPolynomialToG_homogeneous k p n hp
theorem degree_one_independent : LinearIndependent k (fun a : S.AtomExponent => S.initialMonomial k a.val) :=
  S.atom_initial_linearIndependent k
end Run13Presentation
