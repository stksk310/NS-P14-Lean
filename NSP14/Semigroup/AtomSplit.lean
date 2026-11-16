module
public import NSP14.Homological.Presentation
public import NSP14.Semigroup.PolynomialAction
@[expose] public section
open scoped Classical
namespace NSP14.NumericalSemigroup
variable (S : NumericalSemigroup)

/-- The actual multiplicity atom and the actual non-x atoms partition the
full minimal variable set. -/
noncomputable def optionNonXAtomEquiv : Option S.NonXAtom ≃ S.AtomExponent where
  toFun
    | none => ⟨S.multiplicityExponent,S.multiplicity_atom⟩
    | some a => ⟨a.val,a.property.1⟩
  invFun a := if h : a.val.val=S.multiplicity then none else some ⟨a.val,a.property,h⟩
  left_inv a := by
    cases a with
    | none =>
      dsimp only
      split_ifs with h
      · rfl
      · exact False.elim (h rfl)
    | some a =>
      dsimp only
      split_ifs with h
      · exact False.elim (a.property.2 h)
      · rfl
  right_inv a := by
    dsimp only
    split_ifs with h
    · exact Subtype.ext (Subtype.ext h.symm)
    · rfl

theorem optionNonXAtomEquiv_none : S.optionNonXAtomEquiv none=
    ⟨S.multiplicityExponent,S.multiplicity_atom⟩ := rfl

theorem optionNonXAtomEquiv_some (a : S.NonXAtom) :
    S.optionNonXAtomEquiv (some a)=⟨a.val,a.property.1⟩ := rfl
end NSP14.NumericalSemigroup
