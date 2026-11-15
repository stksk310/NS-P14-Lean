module
public import NSP14.Lex.LinearQuotients
public import NSP14.Lex.Hilbert
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open scoped Classical
open NSP14.Homological
attribute [local instance] MvPolynomial.gradedAlgebra
namespace NSP14.Lex
variable (k : Type) [Field k] (q : ℕ)

noncomputable def initialIdeal (m : MonomialOrder (Fin q)) (I : Ideal (MvPolynomial (Fin q) k)) :
    Ideal (MvPolynomial (Fin q) k) :=
  Ideal.span ((fun v => MvPolynomial.monomial v (1:k)) ''
    {v | ∃ p ∈ I,p ≠ 0 ∧ m.degree p=v})

theorem initialIdeal_monomial_mem (m : MonomialOrder (Fin q)) (I : Ideal (MvPolynomial (Fin q) k))
    (v : Fin q →₀ ℕ) :
    MvPolynomial.monomial v (1:k) ∈ initialIdeal k q m I ↔ v ∉ StandardExponent m I := by
  rw [initialIdeal,monomial_mem_span_iff]
  constructor
  · rintro ⟨w,⟨p,hp,hne,rfl⟩,hle⟩ hv
    exact hv p hp hne hle
  · intro hv
    have hex : ∃ p ∈ I,p ≠ 0 ∧ m.degree p ≤ v := by
      simpa only [StandardExponent,Set.mem_ofPred_eq,not_forall,not_not,exists_prop] using hv
    obtain ⟨p,hp,hne,hle⟩ := hex
    exact ⟨m.degree p,⟨p,hp,hne,rfl⟩,hle⟩

theorem initialIdeal_isMonomial (m : MonomialOrder (Fin q)) (I : Ideal (MvPolynomial (Fin q) k)) :
    IsMonomial k q (initialIdeal k q m I) := by
  intro f hf v hv
  obtain ⟨w,hw,hle⟩ := MvPolynomial.mem_ideal_span_monomial_image.mp hf v hv
  exact (monomial_mem_span_iff k q _ v).mpr ⟨w,hw,hle⟩

theorem standardExponent_iff_not_mem {I : Ideal (MvPolynomial (Fin q) k)}
    (hI : IsMonomial k q I) (m : MonomialOrder (Fin q)) (v : Fin q →₀ ℕ) :
    v ∈ StandardExponent m I ↔ MvPolynomial.monomial v (1:k) ∉ I := by
  constructor
  · intro hv hm
    have hn : MvPolynomial.monomial v (1:k) ≠ 0 := by simp
    have hd : m.degree (MvPolynomial.monomial v (1:k))=v := by simp [MonomialOrder.degree_monomial]
    exact hv _ hm hn (by rw [hd])
  · intro hv p hp hne hle
    have hm : MvPolynomial.monomial (m.degree p) (1:k) ∈ I := hI p hp _ (m.degree_mem_support hne)
    exact hv (monomial_mem_of_le k q I _ v hm hle)

theorem initialIdeal_standard (m : MonomialOrder (Fin q)) (I : Ideal (MvPolynomial (Fin q) k)) :
    StandardExponent m (initialIdeal k q m I)=StandardExponent m I := by
  ext v
  rw [standardExponent_iff_not_mem k q (initialIdeal_isMonomial k q m I) m v,
    initialIdeal_monomial_mem]
  exact not_not

theorem initialIdeal_homogeneous (m : MonomialOrder (Fin q)) (I : Ideal (MvPolynomial (Fin q) k)) :
    (initialIdeal k q m I).IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin q) k) := by
  unfold initialIdeal
  apply Ideal.homogeneous_span
  rintro _ ⟨v,_,rfl⟩
  exact ⟨v.degree,MvPolynomial.isHomogeneous_monomial (1:k) rfl⟩

theorem IsMonomial.initialIdeal_eq {I : Ideal (MvPolynomial (Fin q) k)} (hI : IsMonomial k q I)
    (m : MonomialOrder (Fin q)) : initialIdeal k q m I=I := by
  calc
    initialIdeal k q m I=Ideal.span ((fun v => MvPolynomial.monomial v (1:k)) ''
        {v | MvPolynomial.monomial v (1:k) ∈ initialIdeal k q m I}) :=
      (initialIdeal_isMonomial k q m I).span k q
    _=Ideal.span ((fun v => MvPolynomial.monomial v (1:k)) ''
        {v | MvPolynomial.monomial v (1:k) ∈ I}) := by
      congr 2
      ext v
      change MvPolynomial.monomial v (1:k) ∈ initialIdeal k q m I ↔ MvPolynomial.monomial v (1:k) ∈ I
      rw [initialIdeal_monomial_mem,standardExponent_iff_not_mem k q hI]
      exact not_not
    _=I := (hI.span k q).symm

/-- The actual homogeneous quotient and its actual degLex initial ideal
have the same whole Hilbert function. No Betti comparison is asserted here. -/
theorem initialIdeal_sameHilbert (I : Ideal (MvPolynomial (Fin q) k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin q) k)) (n : ℕ) :
    quotientHilbert k q I hI n=quotientHilbert k q (initialIdeal k q MonomialOrder.degLex I)
      (initialIdeal_homogeneous k q MonomialOrder.degLex I) n := by
  change Module.finrank k ({p : StandardExponent MonomialOrder.degLex I // (p.val.degree:ℤ)=(n:ℤ)} →₀ k)=
    Module.finrank k ({p : StandardExponent MonomialOrder.degLex (initialIdeal k q MonomialOrder.degLex I) //
      (p.val.degree:ℤ)=(n:ℤ)} →₀ k)
  rw [initialIdeal_standard]
theorem initialIdeal_span_singleton (m : MonomialOrder (Fin q))
    (p : MvPolynomial (Fin q) k) (hp : p ≠ 0) :
    initialIdeal k q m (Ideal.span {p})=Ideal.span {MvPolynomial.monomial (m.degree p) (1:k)} := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro _ ⟨v,⟨f,hf,hne,rfl⟩,rfl⟩
    obtain ⟨a,rfl⟩ := Ideal.mem_span_singleton.mp hf
    have ha : a ≠ 0 := by intro he; simp [he] at hne
    rw [m.degree_mul hp ha]
    apply monomial_mem_of_le k q _ (m.degree p) _ (Ideal.subset_span (by simp))
    exact le_add_right le_rfl
  · apply Ideal.span_le.mpr
    rintro _ rfl
    exact Ideal.subset_span ⟨m.degree p,⟨p,Ideal.subset_span (by simp),hp,rfl⟩,rfl⟩
end NSP14.Lex
