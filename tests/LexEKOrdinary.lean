module
public import NSP14.Lex.EliahouKervaireOrdinary
@[expose] public section
namespace NSP14.Tests.LexEKOrdinary
theorem actual_ordinary_ek (k : Type) [Field k] (q : ℕ)
    (L : Ideal (MvPolynomial (Fin q) k)) (hproper : L ≠ ⊤) (hL : Lex.IsLex k q L)
    (g : Finset (Fin q →₀ ℕ)) (hg : ∀ v,v ∈ g ↔ Lex.MinimalGenerator k q L v)
    (i : ℕ) (hi : 1 ≤ i) :
    Homological.totalBetti k (Fin q) (ModuleCat.of (MvPolynomial (Fin q) k) ((MvPolynomial (Fin q) k) ⧸ L)) i=
      ∑ v ∈ g,(Lex.maxVariable q v-1).choose (i-1) :=
  Lex.IsLex.ordinary_ek k q hL hproper g hg i hi
end NSP14.Tests.LexEKOrdinary
