module
public import NSP14.Lex.StandardBettiWeights
public import NSP14.Lex.LexTailSupport
@[expose] public section
open scoped Classical BigOperators
open NSP14.Homological
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace NSP14.Lex
variable (k : Type) [Field k] (s r : ℕ)
attribute [local instance] MvPolynomial.gradedAlgebra

theorem standardDegreeGapSum_eq_sum (q : ℕ) (I : Ideal (MvPolynomial (Fin q) k)) (n : ℕ) :
    standardDegreeGapSum k q I n=
      ∑ α : {α : PolynomialDegreeIndex q n // MvPolynomial.monomial α.val (1:k)∉I},(q-maxVariable q α.val.val) := by
  exact Finset.sum_subtype _ (by simp) _

theorem IsLex.suffix_sameGap (I : Ideal (MvPolynomial (Fin (s+r)) k))
    (hI : IsLex k (s+r) I)
    (hHom : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin (s+r)) k))
    (hH2 : quotientHilbert k (s+r) I hHom 2≤Fintype.card (PolynomialDegreeIndex r 2))
    (n : ℕ) (hn : 2≤n) :
    standardDegreeGapSum k r (suffixVariableIdeal k s r I) n=standardDegreeGapSum k (s+r) I n := by
  rw [standardDegreeGapSum_eq_sum,standardDegreeGapSum_eq_sum]
  let e := suffixStandardDegreeEquiv k s r I n
    (fun α hα => hI.standard_tail_support k s r I hHom hH2 α.val (by rw [α.property]; exact hn) hα)
  apply Fintype.sum_equiv e
  intro α
  change r-maxVariable r α.val.val=s+r-maxVariable (s+r) (suffixExponent s r α.val.val)
  have hne : α.val.val≠0 := by intro he; have hh:=α.val.property; rw [he,map_zero] at hh; omega
  rw [suffixExponent_maxVariable s r α.val.val hne]
  omega

theorem IsLex.suffix_sameCorrection (I : Ideal (MvPolynomial (Fin (s+r)) k))
    (hI : IsLex k (s+r) I)
    (hHom : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin (s+r)) k))
    (hH2 : quotientHilbert k (s+r) I hHom 2≤Fintype.card (PolynomialDegreeIndex r 2)) (N : ℕ) :
    lexCorrection k r (suffixVariableIdeal k s r I) N=lexCorrection k (s+r) I N := by
  apply Finset.sum_congr rfl
  intro d _
  exact hI.suffix_sameGap k s r I hHom hH2 (d+2) (by omega)

end NSP14.Lex
