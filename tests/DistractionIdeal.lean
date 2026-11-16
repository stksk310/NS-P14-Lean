module
public import NSP14.Lex.DistractionIdeal
public import NSP14.Lex.Ideal
@[expose] public section
namespace NSP14.Tests.DistractionIdeal
theorem actual_ideal_image (k : Type) [Field k] (q : ℕ)
    (I : Ideal (MvPolynomial (Fin q) (Lex.GenericDistractionField k q)))
    (hI : Lex.IsMonomial (Lex.GenericDistractionField k q) q I) :
    ∃ J : Ideal (MvPolynomial (Fin q) (Lex.GenericDistractionField k q)),
      ∀ f, f∈J ↔ (Lex.genericPolynomialEquiv k q).symm f∈I :=
  ⟨Lex.genericDistractionIdeal k q I, Lex.mem_genericDistractionIdeal k q I hI⟩
end NSP14.Tests.DistractionIdeal
