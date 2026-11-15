module
public import NSP14.Lex.MonomialGenerators
public import Mathlib.RingTheory.Ideal.Colon
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open scoped Classical
namespace NSP14.Lex
variable (k : Type) [Field k] (q : ℕ)

theorem lex_le_of_prefix (v w : Fin q →₀ ℕ) (r : Fin q)
    (hd : v.degree=w.degree) (hp : ∀ i, i < r → v i ≤ w i)
    (hw : ∀ i, r < i → w i=0) :
    MonomialOrder.lex.toSyn v ≤ MonomialOrder.lex.toSyn w := by
  by_contra hn
  have ht : MonomialOrder.lex.toSyn w < MonomialOrder.lex.toSyn v := lt_of_not_ge hn
  change Finsupp.Lex (· < ·) (· < ·) w v at ht
  obtain ⟨i,hi,hiv⟩ := ht
  by_cases hir : i < r
  · have := hp i hir
    omega
  · have hle : w ≤ v := by
      intro j
      by_cases hji : j < i
      · exact (hi j hji).le
      · by_cases hje : j=i
        · subst j; exact hiv.le
        · have hrj : r < j := by omega
          rw [hw j hrj]
          exact Nat.zero_le _
    have hne : w ≠ v := by intro he; rw [he] at hiv; exact (lt_irrefl _ hiv)
    have hs := exponent_degree_strict q hle hne
    omega

def precedes (v w : Fin q →₀ ℕ) : Prop :=
  v.degree < w.degree ∨ v.degree=w.degree ∧ MonomialOrder.lex.toSyn w < MonomialOrder.lex.toSyn v

noncomputable def predecessorIdeal (L : Ideal (MvPolynomial (Fin q) k)) (w : Fin q →₀ ℕ) :
    Ideal (MvPolynomial (Fin q) k) :=
  Ideal.span ((fun v => MvPolynomial.monomial v (1:k)) ''
    {v | MvPolynomial.monomial v (1:k) ∈ L ∧ precedes q v w})

theorem monomial_mem_span_iff (s : Set (Fin q →₀ ℕ)) (v : Fin q →₀ ℕ) :
    MvPolynomial.monomial v (1:k) ∈ Ideal.span ((fun w => MvPolynomial.monomial w (1:k)) '' s) ↔
      ∃ w ∈ s, w ≤ v := by
  rw [MvPolynomial.mem_ideal_span_monomial_image]
  simp [MvPolynomial.support_monomial]

theorem monomial_mem_of_le (L : Ideal (MvPolynomial (Fin q) k))
    (v w : Fin q →₀ ℕ) (hv : MvPolynomial.monomial v (1:k) ∈ L) (hvw : v ≤ w) :
    MvPolynomial.monomial w (1:k) ∈ L := by
  obtain ⟨p,hp⟩ := (MvPolynomial.monomial_dvd_monomial (r:=(1:k)) (s:=(1:k))).mpr
    ⟨Or.inr hvw,dvd_rfl⟩
  rw [hp]
  exact L.mul_mem_right p hv

/-- A generator preceding w cannot divide z*w without using a variable
strictly below the largest variable of w. All membership is in the actual L. -/
theorem IsLex.predecessor_divisor {L : Ideal (MvPolynomial (Fin q) k)}
    (hL : IsLex k q L) (w : Fin q →₀ ℕ) (hw : MinimalGenerator k q L w)
    (r : Fin q) (hr : 0 < w r) (hmax : ∀ i, r < i → w i=0)
    (z v : Fin q →₀ ℕ) (hv : MvPolynomial.monomial v (1:k) ∈ L)
    (hpre : precedes q v w) (hdiv : v ≤ z+w) :
    ∃ i : Fin q, i < r ∧ 0 < z i := by
  by_contra! hn
  have hp : ∀ i, i < r → v i ≤ w i := by
    intro i hi
    have hz := hn i hi
    have hc := hdiv i
    simp only [Finsupp.add_apply] at hc
    omega
  rcases hpre with hdeg|⟨hdeg,hlex⟩
  · let a := w-Finsupp.single r 1
    have hsingle : Finsupp.single r 1 ≤ w := by
      intro i
      by_cases hi : r=i
      · subst i; simpa using (Nat.succ_le_of_lt hr)
      · simp only [Finsupp.single_eq_of_ne' hi]; exact Nat.zero_le _
    have haadd : a+Finsupp.single r 1=w := tsub_add_cancel_of_le hsingle
    have had : a.degree+1=w.degree := by
      have h := congrArg Finsupp.degree haadd
      simpa only [map_add,Finsupp.degree_single] using h
    let v' := v+Finsupp.single r (a.degree-v.degree)
    have hvl : v.degree ≤ a.degree := by omega
    have hvd : v'.degree=a.degree := by
      dsimp only [v']
      rw [map_add,Finsupp.degree_single]
      omega
    have hva : MonomialOrder.lex.toSyn v' ≤ MonomialOrder.lex.toSyn a := by
      apply lex_le_of_prefix q v' a r hvd
      · intro i hi
        have hri : r ≠ i := (ne_of_lt hi).symm
        simpa only [v',a,Finsupp.add_apply,Finsupp.tsub_apply,
          Finsupp.single_eq_of_ne' hri,add_zero,Nat.sub_zero] using hp i hi
      · intro i hi
        simp only [a,Finsupp.tsub_apply,hmax i hi,Nat.zero_sub]
    have hvmem : MvPolynomial.monomial v' (1:k) ∈ L :=
      monomial_mem_of_le k q L v v' hv (by intro i; simp only [v',Finsupp.add_apply]; omega)
    have hamem := hL.2 v' a hvd hva hvmem
    have hal : a ≤ w := by intro i; exact Nat.sub_le _ _
    have hae := hw.2 a hal hamem
    have hd := congrArg Finsupp.degree hae
    omega
  · have hle := lex_le_of_prefix q v w r hdeg hp hmax
    exact (not_lt_of_ge hle hlex)

theorem IsLex.predecessor_colon_monomial {L : Ideal (MvPolynomial (Fin q) k)}
    (hL : IsLex k q L) (w : Fin q →₀ ℕ) (hw : MinimalGenerator k q L w)
    (r : Fin q) (hr : 0 < w r) (hmax : ∀ i, r < i → w i=0)
    (z : Fin q →₀ ℕ) :
    MvPolynomial.monomial z (1:k) ∈
      (predecessorIdeal k q L w).colon {MvPolynomial.monomial w (1:k)} ↔
      ∃ i : Fin q, i < r ∧ 0 < z i := by
  rw [Submodule.mem_colon_singleton]
  change MvPolynomial.monomial z (1:k)*MvPolynomial.monomial w (1:k) ∈ _ ↔ _
  rw [MvPolynomial.monomial_mul_monomial,one_mul]
  change MvPolynomial.monomial (z+w) (1:k) ∈
    Ideal.span ((fun v => MvPolynomial.monomial v (1:k)) ''
      {v | MvPolynomial.monomial v (1:k) ∈ L ∧ precedes q v w}) ↔ _
  rw [monomial_mem_span_iff]
  constructor
  · rintro ⟨v,⟨hv,hpre⟩,hdiv⟩
    exact hL.predecessor_divisor k q w hw r hr hmax z v hv hpre hdiv
  · rintro ⟨i,hi,hzi⟩
    refine ⟨raisedExponent q w i r,⟨hL.raise k q w hw.1 i r hr hi,
      Or.inr ⟨raisedExponent_degree q w i r hr,raisedExponent_lex q w i r hi⟩⟩,?_⟩
    intro j
    by_cases hij : i=j
    · subst j
      have hri : r ≠ i := (ne_of_lt hi).symm
      simp only [raisedExponent,Finsupp.add_apply,Finsupp.tsub_apply,
        Finsupp.single_eq_of_ne' hri,Finsupp.single_eq_same,Nat.sub_zero]
      omega
    · simp only [raisedExponent,Finsupp.add_apply,Finsupp.tsub_apply,
        Finsupp.single_eq_of_ne' hij,add_zero]
      omega

/-- The actual colon at the next lex generator is the ideal of the
variables preceding its largest variable. This constructs no Tor premise. -/
theorem IsLex.predecessor_colon {L : Ideal (MvPolynomial (Fin q) k)}
    (hL : IsLex k q L) (w : Fin q →₀ ℕ) (hw : MinimalGenerator k q L w)
    (r : Fin q) (hr : 0 < w r) (hmax : ∀ i, r < i → w i=0) :
    (predecessorIdeal k q L w).colon {MvPolynomial.monomial w (1:k)} =
      Ideal.span (MvPolynomial.X '' {i : Fin q | i < r}) := by
  apply le_antisymm
  · intro f hf
    apply MvPolynomial.mem_ideal_span_X_image.mpr
    intro z hz
    have hf' : f*MvPolynomial.monomial w (1:k) ∈ predecessorIdeal k q L w :=
      Submodule.mem_colon_singleton.mp hf
    have hz' : z+w ∈ (f*MvPolynomial.monomial w (1:k)).support := by
      rw [MvPolynomial.mem_support_iff,MvPolynomial.coeff_mul_monomial,mul_one]
      exact MvPolynomial.mem_support_iff.mp hz
    obtain ⟨v,⟨hv,hpre⟩,hdiv⟩ := MvPolynomial.mem_ideal_span_monomial_image.mp hf' (z+w) hz'
    obtain ⟨i,hi,hzi⟩ := hL.predecessor_divisor k q w hw r hr hmax z v hv hpre hdiv
    exact ⟨i,hi,ne_of_gt hzi⟩
  · apply Ideal.span_le.mpr
    rintro _ ⟨i,hi,rfl⟩
    change MvPolynomial.monomial (Finsupp.single i 1) (1:k) ∈
      (predecessorIdeal k q L w).colon {MvPolynomial.monomial w (1:k)}
    apply (hL.predecessor_colon_monomial k q w hw r hr hmax _).mpr
    exact ⟨i,hi,by simp⟩

end NSP14.Lex
