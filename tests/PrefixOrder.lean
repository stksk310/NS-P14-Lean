module
public import NSP14.Lex.PrefixOrder
@[expose] public section
open scoped Classical
namespace NSP14.Tests.PrefixOrder
variable (q : ℕ) (p r : Lex.MonomialProfile q)
theorem actual_prefix_order_antisymm
    (hpr : ∀ n (v : Lex.PolynomialDegreeIndex q n),
      (Finset.univ.filter (fun a : Lex.PolynomialDegreeIndex q n =>
        MonomialOrder.degLex.toSyn v.val≤MonomialOrder.degLex.toSyn a.val ∧ p a.val=true)).card≤
      (Finset.univ.filter (fun a : Lex.PolynomialDegreeIndex q n =>
        MonomialOrder.degLex.toSyn v.val≤MonomialOrder.degLex.toSyn a.val ∧ r a.val=true)).card)
    (hrp : ∀ n (v : Lex.PolynomialDegreeIndex q n),
      (Finset.univ.filter (fun a : Lex.PolynomialDegreeIndex q n =>
        MonomialOrder.degLex.toSyn v.val≤MonomialOrder.degLex.toSyn a.val ∧ r a.val=true)).card≤
      (Finset.univ.filter (fun a : Lex.PolynomialDegreeIndex q n =>
        MonomialOrder.degLex.toSyn v.val≤MonomialOrder.degLex.toSyn a.val ∧ p a.val=true)).card) : p=r :=
  Lex.profileDominates_antisymm q hpr hrp
end NSP14.Tests.PrefixOrder
