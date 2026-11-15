module
public import NSP14.Lex.GenericDistractionIteration
@[expose] public section
open scoped Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] MvPolynomial.gradedAlgebra
namespace NSP14.Lex
variable (k : Type) [Field k]

theorem IsStronglyStable.two_variable_transfer
    (I : Ideal (MvPolynomial (Fin 2) k)) (hI : IsStronglyStable k 2 I)
    (w : Fin 2 →₀ ℕ) : ∀ N : ℕ,∀ v : Fin 2 →₀ ℕ,
      w 0-v 0=N → v.degree=w.degree → v 0≤w 0 → MvPolynomial.monomial v (1:k)∈I →
      MvPolynomial.monomial w (1:k)∈I := by
  intro N
  induction N with
  | zero =>
    intro v hN hdeg h0 hv
    have hsum : v 0+v 1=w 0+w 1 := by
      simpa only [Finsupp.degree_eq_sum,Fin.sum_univ_two] using hdeg
    have he0 : v 0=w 0 := by omega
    have he1 : v 1=w 1 := by omega
    have he : v=w := by
      ext i
      have hi : i=0 ∨ i=1 := by omega
      rcases hi with rfl|rfl
      · exact he0
      · exact he1
    simpa only [he] using hv
  | succ N ih =>
    intro v hN hdeg h0 hv
    have hsum : v 0+v 1=w 0+w 1 := by
      simpa only [Finsupp.degree_eq_sum,Fin.sum_univ_two] using hdeg
    have hv1 : 0<v 1 := by omega
    let z := raisedExponent 2 v 0 1
    have hz0 : z 0=v 0+1 := by simp [z,raisedExponent]
    have hzd : z.degree=w.degree := (raisedExponent_degree 2 v 0 1 hv1).trans hdeg
    have hzmem := hI.2 v hv 0 1 hv1 (by decide)
    exact ih z (by omega) hzd (by omega) hzmem

theorem IsStronglyStable.isLex_two
    (I : Ideal (MvPolynomial (Fin 2) k)) (hI : IsStronglyStable k 2 I) : IsLex k 2 I := by
  refine ⟨hI.1,?_⟩
  intro v w hdeg hlex hv
  have h0 : v 0≤w 0 := by
    by_contra hn
    have hlt : MonomialOrder.lex.toSyn w<MonomialOrder.lex.toSyn v := by
      change Finsupp.Lex (· < ·) (· < ·) w v
      exact ⟨0,fun i hi => False.elim (by omega),by omega⟩
    exact not_lt_of_ge hlex hlt
  exact hI.two_variable_transfer k I w (w 0-v 0) v rfl hdeg h0 hv

theorem IsStronglyStable.isLex_of_le_two (q : ℕ) (hq : q≤2)
    (I : Ideal (MvPolynomial (Fin q) k)) (hI : IsStronglyStable k q I) : IsLex k q I := by
  cases q with
  | zero =>
    refine ⟨hI.1,?_⟩
    intro v w _ _ hv
    have he : v=w := Subsingleton.elim _ _
    simpa only [he] using hv
  | succ q =>
    cases q with
    | zero =>
      refine ⟨hI.1,?_⟩
      intro v w hdeg _ hv
      have he0 : v 0=w 0 := by
        rw [Finsupp.degree_eq_sum,Finsupp.degree_eq_sum] at hdeg
        change (∑ i : Fin 1,v i)=(∑ i : Fin 1,w i) at hdeg
        simpa using hdeg
      have he : v=w := by
        ext i
        have hi : i=0 := by omega
        simpa only [hi] using he0
      simpa only [he] using hv
    | succ q =>
      cases q with
      | zero => exact hI.isLex_two k I
      | succ q => omega
end NSP14.Lex

namespace NSP14.Lex
variable (k : Type) [Field k] (q : ℕ)
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Actual BHP comparison in zero, one or two variables, for all rows and internal degrees. -/
theorem quotientGradedBetti_le_lex_of_le_two (hq : q≤2)
    (I L : Ideal (MvPolynomial (Fin q) k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin q) k))
    (hL : L.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin q) k))
    (hlL : IsLex k q L) (hH : ∀ n,quotientHilbert k q I hI n=quotientHilbert k q L hL n)
    (i : ℕ) (t : ℤ) : quotientGradedBetti k q I hI i t≤quotientGradedBetti k q L hL i t := by
  obtain ⟨F,fieldF,hA,J,hJ,hmono,hstable,hHF,hbetti⟩ := exists_stronglyStable_comparison k q I hI
  let : Field F := fieldF
  let : Algebra k F := hA
  have hlexJ : IsLex F q J := IsStronglyStable.isLex_of_le_two F q hq J ⟨hmono,hstable⟩
  have he : J=monomialExtension k F q L :=
    IsLex.eq_of_sameHilbert F q J _ hJ (monomialExtension_homogeneous k F q L) hlexJ
      (monomialExtension_isLex k F q L hlL) (fun n => (hHF n).symm.trans
        ((hH n).trans (monomialExtension_sameHilbert k F q L hL hlL.1 n)))
  have hb : quotientGradedBetti F q J hJ i t=quotientGradedBetti k q L hL i t := by
    simpa only [he] using monomialExtension_gradedBetti k F q L hL hlL.1 i t
  exact (hbetti i t).trans_eq hb

/-- A single actual lex ideal with the same whole Hilbert function in at most two variables. -/
theorem exists_lex_sameHilbert_of_le_two (hq : q≤2)
    (I : Ideal (MvPolynomial (Fin q) k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin q) k)) :
    ∃ (L : Ideal (MvPolynomial (Fin q) k))
      (hL : L.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin q) k)),
      IsLex k q L ∧ ∀ n,quotientHilbert k q I hI n=quotientHilbert k q L hL n := by
  obtain ⟨F,fieldF,_,J,hJ,hmono,hstable,hHF,_⟩ := exists_stronglyStable_comparison k q I hI
  let : Field F := fieldF
  have hlexJ : IsLex F q J := IsStronglyStable.isLex_of_le_two F q hq J ⟨hmono,hstable⟩
  exact ⟨monomialExtension F k q J,monomialExtension_homogeneous F k q J,
    monomialExtension_isLex F k q J hlexJ,
    fun n => (hHF n).trans (monomialExtension_sameHilbert F k q J hJ hmono n)⟩
end NSP14.Lex
