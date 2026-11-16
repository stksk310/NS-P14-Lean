module
public import NSP14.Lex.DegreeSeparator
public import NSP14.Lex.ColexRestriction
public import NSP14.Lex.Uniqueness
@[expose] public section
open scoped Classical BigOperators FinsetFamily
open Finset
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] MvPolynomial.gradedAlgebra
namespace NSP14.Lex
variable (k : Type) [Field k] (q d : ℕ)

def degreeIdealFamily (I : Ideal (MvPolynomial (Fin (q+1)) k)) : Finset (Finset (Fin (d+q))) :=
  (Finset.univ.filter (fun α : PolynomialDegreeIndex (q+1) d => MvPolynomial.monomial α.val (1:k)∈I)).image
    (degreeSeparator q d)

theorem degreeIdealFamily_sized (I : Ideal (MvPolynomial (Fin (q+1)) k)) :
    (degreeIdealFamily k q d I : Set (Finset (Fin (d+q)))).Sized q := by
  rintro B hB
  obtain ⟨α,_,rfl⟩ := Finset.mem_image.mp hB
  exact degreeSeparator_card q d α

theorem degreeIdealFamily_isInitSeg (I : Ideal (MvPolynomial (Fin (q+1)) k))
    (hI : IsLex k (q+1) I) : Finset.Colex.IsInitSeg (degreeIdealFamily k q d I) q := by
  refine ⟨degreeIdealFamily_sized k q d I,?_⟩
  intro B T hB hTB
  obtain ⟨α,hα,rfl⟩ := Finset.mem_image.mp hB
  simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hα
  let β := (degreeSeparatorEquiv q d).symm ⟨T,hTB.2⟩
  have hβ : degreeSeparator q d β=T := by
    have hh := congrArg Subtype.val ((degreeSeparatorEquiv q d).apply_symm_apply ⟨T,hTB.2⟩)
    exact hh
  have hlex : MonomialOrder.lex.toSyn α.val<MonomialOrder.lex.toSyn β.val :=
    (degreeSeparator_colex_lt_iff q d β α).mp (by simpa only [hβ] using hTB.1)
  apply Finset.mem_image.mpr
  refine ⟨β,?_,hβ⟩
  simp only [Finset.mem_filter,Finset.mem_univ,true_and]
  exact hI.2 α.val β.val (α.property.trans β.property.symm) hlex.le hα

theorem degreeIdealFamily_card (I : Ideal (MvPolynomial (Fin (q+1)) k)) :
    (degreeIdealFamily k q d I).card=
      Fintype.card {α : PolynomialDegreeIndex (q+1) d // MvPolynomial.monomial α.val (1:k)∈I} := by
  rw [degreeIdealFamily,Finset.card_image_of_injective _ (degreeSeparator_injective q d),Fintype.card_subtype]

theorem degreeIdealFamily_card_add_hilbert (I : Ideal (MvPolynomial (Fin (q+1)) k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin (q+1)) k))
    (hmono : IsMonomial k (q+1) I) :
    (degreeIdealFamily k q d I).card+quotientHilbert k (q+1) I hI d=
      Fintype.card (PolynomialDegreeIndex (q+1) d) := by
  rw [degreeIdealFamily_card,quotientHilbert_eq_standard_card]
  simp_rw [standardExponent_iff_not_mem k (q+1) hmono]
  rw [Fintype.card_subtype_compl]
  have hle := Fintype.card_subtype_le (fun α : PolynomialDegreeIndex (q+1) d => MvPolynomial.monomial α.val (1:k)∈I)
  omega

theorem degreeIdealFamily_zeroLink_card (I : Ideal (MvPolynomial (Fin (q+2)) k)) :
    (zeroLinkFamily (degreeIdealFamily k (q+1) d I)).card=
      (Finset.univ.filter (fun α : PolynomialDegreeIndex (q+2) d =>
        MvPolynomial.monomial α.val (1:k)∈I ∧ α.val (Fin.last (q+1))=0)).card := by
  rw [zeroLinkFamily_card,degreeIdealFamily,Finset.filter_image]
  simp_rw [degreeSeparator_zero_mem]
  rw [Finset.card_image_of_injective _ (degreeSeparator_injective (q+1) d),Finset.filter_filter]
end NSP14.Lex

namespace NSP14.Lex
variable (k : Type) [Field k] (q d : ℕ)
attribute [local instance] MvPolynomial.gradedAlgebra
theorem monomialDegreeCard_add_hilbert (I : Ideal (MvPolynomial (Fin (q+1)) k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin (q+1)) k))
    (hmono : IsMonomial k (q+1) I) :
    Fintype.card {α : PolynomialDegreeIndex (q+1) d // MvPolynomial.monomial α.val (1:k)∈I}+
      quotientHilbert k (q+1) I hI d=Fintype.card (PolynomialDegreeIndex (q+1) d) := by
  rw [← degreeIdealFamily_card k q d I]
  exact degreeIdealFamily_card_add_hilbert k q d I hI hmono
end NSP14.Lex
