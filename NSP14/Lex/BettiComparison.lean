module
public import NSP14.Lex.StableBettiComparison
@[expose] public section
open scoped Classical BigOperators
open NSP14.Homological
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace NSP14.Lex
variable (k : Type) [Field k] (q : ℕ)
attribute [local instance] MvPolynomial.gradedAlgebra
/-- Arbitrary-characteristic comparison for the actual graded quotient Betti numbers. -/
theorem quotientGradedBetti_le_lex
    (I L : Ideal (MvPolynomial (Fin q) k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin q) k))
    (hL : L.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin q) k))
    (hlL : IsLex k q L) (hH : ∀ n,quotientHilbert k q I hI n=quotientHilbert k q L hL n)
    (i : ℕ) (hi : 1 ≤ i) (t : ℤ) : quotientGradedBetti k q I hI i t≤quotientGradedBetti k q L hL i t := by
  obtain ⟨F,fieldF,hA,J,hJ,hmono,hstable,hHF,hbetti⟩ := exists_stronglyStable_comparison k q I hI
  let : Field F := fieldF
  let : Algebra k F := hA
  have hlexLF := monomialExtension_isLex k F q L hlL
  have hHFJF (n : ℕ) : quotientHilbert F q J hJ n=
      quotientHilbert F q (monomialExtension k F q L) (monomialExtension_homogeneous k F q L) n :=
    (hHF n).symm.trans ((hH n).trans (monomialExtension_sameHilbert k F q L hL hlL.1 n))
  have hb := IsStronglyStable.graded_betti_le_lex F q J (monomialExtension k F q L)
    ⟨hmono,hstable⟩ hlexLF hJ (monomialExtension_homogeneous k F q L) hHFJF i hi t
  exact (hbetti i t).trans (hb.trans_eq (monomialExtension_gradedBetti k F q L hL hlL.1 i t))
end NSP14.Lex
