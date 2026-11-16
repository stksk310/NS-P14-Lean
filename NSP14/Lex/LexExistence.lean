module
public import NSP14.Lex.LexCompatibleDegrees
@[expose] public section
open scoped Classical BigOperators
open NSP14.Homological
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace NSP14.Lex
variable (k : Type) [Field k] (q : ℕ) (I : Ideal (MvPolynomial (Fin q) k))
attribute [local instance] MvPolynomial.gradedAlgebra
def lexProfileSupport : Set (Fin q →₀ ℕ) :=
  {v | (⟨v,rfl⟩ : PolynomialDegreeIndex q v.degree)∈lexDegreeSet k q I v.degree}

theorem lexProfileSupport_degree_mem (n : ℕ) (α : PolynomialDegreeIndex q n) :
    α.val∈lexProfileSupport k q I ↔ α∈lexDegreeSet k q I n := by
  rcases α with ⟨v,hv⟩
  subst n
  rfl

theorem IsStronglyStable.lexProfileSupport_next (hI : IsStronglyStable k q I)
    (v : Fin q →₀ ℕ) (hv : v∈lexProfileSupport k q I) (r : Fin q) :
    v+Finsupp.single r 1∈lexProfileSupport k q I := by
  have hh := hI.lexDegreeSet_next_mem k q I v.degree ⟨v,rfl⟩ hv r
  exact (lexProfileSupport_degree_mem k q I (v.degree+1)
    ⟨v+Finsupp.single r 1,by simp only [map_add,Finsupp.degree_single]⟩).mpr hh

theorem exponent_predicate_add (q : ℕ) (P : (Fin q →₀ ℕ) → Prop)
    (hP : ∀ v,P v → ∀ r,P (v+Finsupp.single r 1))
    (v γ : Fin q →₀ ℕ) (hv : P v) : P (v+γ) := by
  induction γ using Finsupp.induction₂ with
  | zero => simpa only [add_zero] using hv
  | add_single r n γ _ _ ih =>
    have hh : ∀ m : ℕ,P (v+γ+Finsupp.single r m) := by
      intro m
      induction m with
      | zero => simpa only [Finsupp.single_zero,add_zero] using ih
      | succ m ihm =>
        simpa only [Finsupp.single_add,← add_assoc] using hP _ ihm r
    simpa only [add_assoc] using hh n

def lexProfileIdeal : Ideal (MvPolynomial (Fin q) k) :=
  Ideal.span ((fun v => MvPolynomial.monomial v (1:k)) '' lexProfileSupport k q I)

theorem lexProfileIdeal_isMonomial : IsMonomial k q (lexProfileIdeal k q I) := by
  intro f hf v hv
  obtain ⟨w,hw,hle⟩ := MvPolynomial.mem_ideal_span_monomial_image.mp hf v hv
  exact (monomial_mem_span_iff k q _ v).mpr ⟨w,hw,hle⟩

theorem lexProfileIdeal_homogeneous :
    (lexProfileIdeal k q I).IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin q) k) := by
  apply Ideal.homogeneous_span
  rintro _ ⟨v,_,rfl⟩
  exact ⟨v.degree,MvPolynomial.isHomogeneous_monomial (1:k) rfl⟩

theorem IsStronglyStable.lexProfileIdeal_monomial_mem (hI : IsStronglyStable k q I) (v : Fin q →₀ ℕ) :
    MvPolynomial.monomial v (1:k)∈lexProfileIdeal k q I ↔ v∈lexProfileSupport k q I := by
  rw [lexProfileIdeal,monomial_mem_span_iff]
  constructor
  · rintro ⟨w,hw,hle⟩
    have hh := exponent_predicate_add q (fun z => z∈lexProfileSupport k q I)
      (fun a ha r => hI.lexProfileSupport_next k q I a ha r) w (v-w) hw
    simpa only [add_tsub_cancel_of_le hle] using hh
  · intro hv
    exact ⟨v,hv,le_rfl⟩

theorem IsStronglyStable.lexProfileIdeal_degree_mem (hI : IsStronglyStable k q I)
    (n : ℕ) (α : PolynomialDegreeIndex q n) :
    MvPolynomial.monomial α.val (1:k)∈lexProfileIdeal k q I ↔ α∈lexDegreeSet k q I n := by
  rw [hI.lexProfileIdeal_monomial_mem k q I,lexProfileSupport_degree_mem]

theorem IsStronglyStable.lexProfileIdeal_degreeCard (hI : IsStronglyStable k q I) (n : ℕ) :
    idealDegreeCard k q (lexProfileIdeal k q I) n=idealDegreeCard k q I n := by
  simp only [idealDegreeCard,Fintype.card_subtype,hI.lexProfileIdeal_degree_mem k q I n]
  rw [Finset.filter_mem_eq_inter,Finset.univ_inter]
  simpa only [idealDegreeCard,Fintype.card_subtype] using lexDegreeSet_card k q I n

theorem IsStronglyStable.lexProfileIdeal_isLex (hI : IsStronglyStable k q I) :
    IsLex k q (lexProfileIdeal k q I) := by
  refine ⟨lexProfileIdeal_isMonomial k q I,?_⟩
  intro v w hdeg hlex hv
  rw [hI.lexProfileIdeal_monomial_mem k q I] at hv ⊢
  have hh := lexDegreeSet_upper k q I v.degree ⟨v,rfl⟩ hv ⟨w,hdeg.symm⟩ hlex
  exact (lexProfileSupport_degree_mem k q I v.degree ⟨w,hdeg.symm⟩).mpr hh

theorem IsStronglyStable.lexProfileIdeal_sameHilbert (hI : IsStronglyStable k q I)
    (hHom : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin q) k)) (n : ℕ) :
    quotientHilbert k q I hHom n=
      quotientHilbert k q (lexProfileIdeal k q I) (lexProfileIdeal_homogeneous k q I) n := by
  have hi := idealDegreeCard_add_hilbert k q I hHom hI.1 n
  have hl := idealDegreeCard_add_hilbert k q (lexProfileIdeal k q I) (lexProfileIdeal_homogeneous k q I)
    (lexProfileIdeal_isMonomial k q I) n
  rw [hI.lexProfileIdeal_degreeCard k q I n] at hl
  omega

/-- A single actual lex ideal realizes the entire Hilbert function of any homogeneous quotient. -/
theorem exists_lex_sameHilbert
    (hHom : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin q) k)) :
    ∃ (L : Ideal (MvPolynomial (Fin q) k))
      (hL : L.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin q) k)),
      IsLex k q L ∧ ∀ n,quotientHilbert k q I hHom n=quotientHilbert k q L hL n := by
  obtain ⟨F,fieldF,_,J,hJ,hmono,hstable,hHF,_⟩ := exists_stronglyStable_comparison k q I hHom
  let : Field F := fieldF
  have hsJ : IsStronglyStable F q J := ⟨hmono,hstable⟩
  let LJ := lexProfileIdeal F q J
  have hlLJ : IsLex F q LJ := hsJ.lexProfileIdeal_isLex F q J
  exact ⟨monomialExtension F k q LJ,monomialExtension_homogeneous F k q LJ,
    monomialExtension_isLex F k q LJ hlLJ,
    fun n => (hHF n).trans ((hsJ.lexProfileIdeal_sameHilbert F q J hJ n).trans
      (monomialExtension_sameHilbert F k q LJ (lexProfileIdeal_homogeneous F q J) hlLJ.1 n))⟩
end NSP14.Lex
