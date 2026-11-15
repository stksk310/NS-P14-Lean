module
public import NSP14.Lex.GenericDistractionStable
@[expose] public section
namespace NSP14.Tests.GenericDistractionStable
variable (k : Type) [Field k] (q : ℕ)

theorem actual_fixed_support_raise (I : Ideal (MvPolynomial (Fin q) k))
    (hmono : Lex.IsMonomial k q I)
    (hfix : ∀ v,MvPolynomial.monomial v (1:Lex.GenericDistractionField k q)∈Lex.genericMonomialStep k q I ↔
      MvPolynomial.monomial v (1:k)∈I)
    (v : Fin q →₀ ℕ) (hv : MvPolynomial.monomial v (1:k)∈I)
    (a b : Fin q) (hb : 0<v b) (hab : a<b) :
    MvPolynomial.monomial (Lex.raisedExponent q v a b) (1:k)∈I :=
  Lex.genericMonomialStep_fixed_raise k q I hmono hfix v hv a b hb hab
end NSP14.Tests.GenericDistractionStable
