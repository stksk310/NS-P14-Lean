module
public import NSP14.Lex.LexExistence
public import Mathlib.Algebra.Field.ZMod
@[expose] public section
open scoped Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace NSP14.Tests.LexHilbertExamples
open NSP14.Lex
attribute [local instance] MvPolynomial.gradedAlgebra
variable (k : Type) [Field k]
noncomputable def twoQuadrics : Ideal (MvPolynomial (Fin 3) k) :=
  Ideal.span ((fun v : Fin 3 →₀ ℕ => MvPolynomial.monomial v (1:k)) ''
    {Finsupp.single 0 2,Finsupp.single 1 2})

theorem twoQuadrics_homogeneous :
    (twoQuadrics k).IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin 3) k) := by
  apply Ideal.homogeneous_span
  rintro _ ⟨v,_,rfl⟩
  exact ⟨v.degree,MvPolynomial.isHomogeneous_monomial (1:k) rfl⟩

theorem twoQuadrics_not_lex : ¬IsLex k 3 (twoQuadrics k) := by
  intro hlex
  let v : Fin 3 →₀ ℕ := Finsupp.single 1 2
  let w : Fin 3 →₀ ℕ := Finsupp.single 0 1+Finsupp.single 1 1
  have hv : MvPolynomial.monomial v (1:k)∈twoQuadrics k :=
    Ideal.subset_span ⟨v,Or.inr rfl,rfl⟩
  have hw : MvPolynomial.monomial w (1:k)∉twoQuadrics k := by
    rw [twoQuadrics,monomial_mem_span_iff]
    rintro ⟨a,ha,hle⟩
    rcases ha with rfl|rfl
    · have hh := hle 0
      simp only [w,Finsupp.add_apply,Finsupp.single_eq_same,Finsupp.single_eq_of_ne' (by decide : (1:Fin 3)≠0),add_zero] at hh
      omega
    · have hh := hle 1
      simp only [w,Finsupp.add_apply,Finsupp.single_eq_same,Finsupp.single_eq_of_ne' (by decide : (0:Fin 3)≠1),zero_add] at hh
      omega
  have hvw : MonomialOrder.lex.toSyn v<MonomialOrder.lex.toSyn w := by
    change Finsupp.Lex (· < ·) (· < ·) v w
    refine ⟨0,?_,?_⟩
    · intro j hj
      exact False.elim (by omega)
    · simp [v,w]
  exact hw (hlex.2 v w (by simp [v,w]) hvw.le hv)

def ActualLexComparison : Prop := ∃ (L : Ideal (MvPolynomial (Fin 3) k))
    (hL : L.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin 3) k)),
    IsLex k 3 L ∧ (∀ n,quotientHilbert k 3 (twoQuadrics k) (twoQuadrics_homogeneous k) n=quotientHilbert k 3 L hL n) ∧
    ∀ i : ℕ,1 ≤ i → ∀ j : ℤ,
      quotientGradedBetti k 3 (twoQuadrics k) (twoQuadrics_homogeneous k) i j≤quotientGradedBetti k 3 L hL i j

theorem twoQuadrics_actual_comparison : ActualLexComparison k := by
  obtain ⟨L,hL,hlex,hHF⟩ := exists_lex_sameHilbert k 3 (twoQuadrics k) (twoQuadrics_homogeneous k)
  exact ⟨L,hL,hlex,hHF,fun i hi j => quotientGradedBetti_le_lex k 3 _ L (twoQuadrics_homogeneous k) hL hlex hHF i hi j⟩
theorem actual_char0 : ActualLexComparison ℚ := twoQuadrics_actual_comparison ℚ
theorem actual_char2 : ActualLexComparison (ZMod 2) := twoQuadrics_actual_comparison (ZMod 2)
theorem actual_char3 : ActualLexComparison (ZMod 3) := twoQuadrics_actual_comparison (ZMod 3)
end NSP14.Tests.LexHilbertExamples
