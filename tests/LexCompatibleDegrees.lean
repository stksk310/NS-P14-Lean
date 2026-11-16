module
public import NSP14.Lex.LexCompatibleDegrees
@[expose] public section
namespace NSP14.Tests.LexCompatibleDegrees
variable (k : Type) [Field k] (q n : ℕ)
theorem actual_degree_compatibility (I : Ideal (MvPolynomial (Fin q) k)) (hI : Lex.IsStronglyStable k q I)
    (α : Lex.PolynomialDegreeIndex q n) (hα : α∈Lex.lexDegreeSet k q I n) (r : Fin q) :
    (⟨α.val+Finsupp.single r 1,by simp only [map_add,Finsupp.degree_single,α.property]⟩ : Lex.PolynomialDegreeIndex q (n+1))∈Lex.lexDegreeSet k q I (n+1) :=
  Lex.IsStronglyStable.lexDegreeSet_next_mem k q I hI n α hα r
end NSP14.Tests.LexCompatibleDegrees
