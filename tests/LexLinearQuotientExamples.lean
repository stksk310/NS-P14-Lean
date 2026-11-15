module
public import NSP14.Lex.EliahouKervaireOrdinary
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Tactic.FinCases
@[expose] public section
open scoped Classical
namespace NSP14.Tests.LexLinearQuotientExamples
variable (k : Type) [Field k]

noncomputable def mixedIdeal : Ideal (MvPolynomial (Fin 2) k) :=
  Ideal.span ((fun v => MvPolynomial.monomial v (1:k)) ''
    {Finsupp.single (0:Fin 2) 1,Finsupp.single (1:Fin 2) 2})

theorem mixed_monomial (v : Fin 2 →₀ ℕ) :
    MvPolynomial.monomial v (1:k) ∈ mixedIdeal k ↔ 0 < v 0 ∨ 2 ≤ v 1 := by
  rw [mixedIdeal,Lex.monomial_mem_span_iff]
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff]
  constructor
  · rintro ⟨w,hw,hle⟩
    rcases hw with rfl|rfl
    · left; have := Finsupp.single_le_iff.mp hle; omega
    · exact Or.inr (Finsupp.single_le_iff.mp hle)
  · intro hv
    rcases hv with hv|hv
    · exact ⟨_,Or.inl rfl,Finsupp.single_le_iff.mpr (by omega)⟩
    · exact ⟨_,Or.inr rfl,Finsupp.single_le_iff.mpr hv⟩

theorem mixed_lex : Lex.IsLex k 2 (mixedIdeal k) := by
  constructor
  · intro f hf v hv
    apply (Lex.monomial_mem_span_iff k 2 _ v).mpr
    exact MvPolynomial.mem_ideal_span_monomial_image.mp hf v hv
  · intro v w hdeg hlex hv
    have h0 : v 0 ≤ w 0 := by
      by_contra hn
      have hl : MonomialOrder.lex.toSyn w < MonomialOrder.lex.toSyn v := by
        change Finsupp.Lex (· < ·) (· < ·) w v
        refine ⟨0,?_,by omega⟩
        intro i hi
        change i.val < 0 at hi
        omega
      exact not_lt_of_ge hlex hl
    rw [mixed_monomial] at hv ⊢
    rcases hv with hv|hv
    · left; omega
    · by_cases hw0 : 0 < w 0
      · exact Or.inl hw0
      · right
        simp only [Finsupp.degree_eq_sum,Fin.sum_univ_two] at hdeg
        omega

theorem mixed_y_square_minimal : Lex.MinimalGenerator k 2 (mixedIdeal k) (Finsupp.single (1:Fin 2) 2) := by
  refine ⟨(mixed_monomial k _).mpr (Or.inr (by simp)),?_⟩
  intro v hv hm
  have h0 := hv 0
  have h1 := hv 1
  simp only [Finsupp.single_eq_of_ne (by decide : (0:Fin 2) ≠ 1)] at h0
  simp only [Finsupp.single_eq_same] at h1
  rw [mixed_monomial] at hm
  have hz : v 0=0 := by omega
  have ho : v 1=2 := by omega
  ext i
  fin_cases i <;> simp [hz,ho]

/-- A genuine lex ideal with generator degrees 1 and 2, not an empty
predicate instance. The colon result is applied over every coefficient field. -/
def MixedColon : Prop :=
    (Lex.predecessorIdeal k 2 (mixedIdeal k) (Finsupp.single (1:Fin 2) 2)).colon
      {MvPolynomial.monomial (Finsupp.single (1:Fin 2) 2) (1:k)} =
      Ideal.span ((MvPolynomial.X : Fin 2 → MvPolynomial (Fin 2) k) '' {i : Fin 2 | i < 1})

theorem mixed_y_square_colon : MixedColon k := by
  apply (mixed_lex k).predecessor_colon k 2 _ (mixed_y_square_minimal k) 1 (by simp)
  intro i hi
  have := i.isLt
  change 1 < i.val at hi
  omega

theorem mixed_y_square_colon_char2 : MixedColon (ZMod 2) := mixed_y_square_colon (ZMod 2)
theorem mixed_y_square_colon_char3 : MixedColon (ZMod 3) := mixed_y_square_colon (ZMod 3)
theorem mixed_y_square_colon_char0 : MixedColon ℚ := mixed_y_square_colon ℚ

theorem mixed_x_minimal : Lex.MinimalGenerator k 2 (mixedIdeal k) (Finsupp.single (0:Fin 2) 1) := by
  refine ⟨(mixed_monomial k _).mpr (Or.inl (by simp)),?_⟩
  intro v hv hm
  have h0 := hv 0
  have h1 := hv 1
  simp only [Finsupp.single_eq_same] at h0
  simp only [Finsupp.single_eq_of_ne (by decide : (1:Fin 2) ≠ 0)] at h1
  rw [mixed_monomial] at hm
  have hz : v 0=1 := by omega
  have ho : v 1=0 := by omega
  ext i
  fin_cases i <;> simp [hz,ho]

theorem mixed_proper : mixedIdeal k ≠ ⊤ := by
  intro he
  have hm : MvPolynomial.monomial (0 : Fin 2 →₀ ℕ) (1:k) ∈ mixedIdeal k := by rw [he]; trivial
  have h := (mixed_monomial k _).mp hm
  simp only [Finsupp.zero_apply,lt_self_iff_false,Nat.reduceLeDiff,or_self] at h

theorem mixed_minimal_set (v : Fin 2 →₀ ℕ) :
    v ∈ ({Finsupp.single (0:Fin 2) 1,Finsupp.single (1:Fin 2) 2} : Finset (Fin 2 →₀ ℕ)) ↔
      Lex.MinimalGenerator k 2 (mixedIdeal k) v := by
  constructor
  · intro h
    simp only [Finset.mem_insert,Finset.mem_singleton] at h
    rcases h with rfl|rfl
    · exact mixed_x_minimal k
    · exact mixed_y_square_minimal k
  · intro h
    have hm := (mixed_monomial k v).mp h.1
    rcases hm with hx|hy
    · have he := h.2 (Finsupp.single 0 1) (Finsupp.single_le_iff.mpr (by omega)) (mixed_x_minimal k).1
      simp only [Finset.mem_insert,Finset.mem_singleton]
      exact Or.inl he.symm
    · have he := h.2 (Finsupp.single 1 2) (Finsupp.single_le_iff.mpr hy) (mixed_y_square_minimal k).1
      simp only [Finset.mem_insert,Finset.mem_singleton]
      exact Or.inr he.symm

def MixedOrdinaryRows : Prop :=
  Homological.totalBetti k (Fin 2)
    (ModuleCat.of (MvPolynomial (Fin 2) k) ((MvPolynomial (Fin 2) k) ⧸ mixedIdeal k)) 1=2 ∧
  Homological.totalBetti k (Fin 2)
    (ModuleCat.of (MvPolynomial (Fin 2) k) ((MvPolynomial (Fin 2) k) ⧸ mixedIdeal k)) 2=1 ∧
  Homological.totalBetti k (Fin 2)
    (ModuleCat.of (MvPolynomial (Fin 2) k) ((MvPolynomial (Fin 2) k) ⧸ mixedIdeal k)) 3=0

theorem mixed_ordinary_rows : MixedOrdinaryRows k := by
  have h1 := (mixed_lex k).ordinary_ek k 2 (mixed_proper k) _ (mixed_minimal_set k) 1 (by omega)
  have h2 := (mixed_lex k).ordinary_ek k 2 (mixed_proper k) _ (mixed_minimal_set k) 2 (by omega)
  have h3 := (mixed_lex k).ordinary_ek k 2 (mixed_proper k) _ (mixed_minimal_set k) 3 (by omega)
  have hne : Finsupp.single (0:Fin 2) 1 ≠ Finsupp.single (1:Fin 2) 2 := by
    intro he
    have h := congrArg (fun v : Fin 2 →₀ ℕ => v 0) he
    norm_num at h
  norm_num [Lex.maxVariable,hne] at h1 h2 h3
  exact ⟨h1,h2,h3⟩

theorem mixed_ordinary_rows_char2 : MixedOrdinaryRows (ZMod 2) := mixed_ordinary_rows (ZMod 2)
theorem mixed_ordinary_rows_char3 : MixedOrdinaryRows (ZMod 3) := mixed_ordinary_rows (ZMod 3)
theorem mixed_ordinary_rows_char0 : MixedOrdinaryRows ℚ := mixed_ordinary_rows ℚ
end NSP14.Tests.LexLinearQuotientExamples
