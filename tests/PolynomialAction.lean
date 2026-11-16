module

public import NSP14
public import tests.Run12BasicExamples

@[expose] public section

noncomputable section
open NSP14 NSP14.NumericalSemigroup
open scoped Classical

section Generic
variable (S : NumericalSemigroup) (k : Type*) [CommRing k] [Nontrivial k]
example : Fintype.card S.NonXAtom=S.embeddingDimension-1 := S.nonXAtom_card
example : Function.Surjective (S.polynomialToA k) := S.polynomialToA_surjective k
example : Function.Surjective (S.polynomialToQ k) := S.polynomialToQ_surjective k
example (a : S.NonXAtom) : S.polynomialToG k (MvPolynomial.X a)=S.initialMonomial k a.val := S.polynomialToG_X k a
example (p : S.PolynomialRing k) (a : (S.xMultiply k).ker) :
    (p • a).val = S.polynomialToG k p * a.val := S.polynomial_smul_T k p a
example (p : S.PolynomialRing k) (a : (S.nonAperyIdeal k).restrictScalars k) :
    (p • a).val = S.polynomialToA k p * a.val := S.polynomial_smul_N k p a
example (p q : S.PolynomialRing k) (a b : (S.xMultiply k).ker) :
    (p+q) • (a+b)=p•a+p•b+(q•a+q•b) := by rw [add_smul,smul_add,smul_add]
example (c : k) (p : S.PolynomialRing k) (a : (S.nonAperyIdeal k).restrictScalars k) :
    (c • p) • a=c • (p • a) := smul_assoc c p a
example (p : S.PolynomialRing k) (a : S.TangentAlgebra k) :
    S.polynomialGtoA k (p•a)=p • S.polynomialGtoA k a := map_smul _ _ _
example (p : S.PolynomialRing k) (a : S.HeadAlgebra k) :
    S.polynomialAtoQ k (p•a)=p • S.polynomialAtoQ k a := map_smul _ _ _
end Generic

namespace PolynomialExamples
open AperyQuotientExamples
example : Fintype.card naturals.NonXAtom=0 := by rw [naturals.nonXAtom_card,naturals_e]
example : Function.Surjective (naturals.polynomialToA (ZMod 2)) := naturals.polynomialToA_surjective (ZMod 2)
example : Function.Surjective (naturals.polynomialToQ ℚ) := naturals.polynomialToQ_surjective ℚ

def two : NumericalSemigroup where
  carrier :=
    { carrier := {n | n=0 ∨ 2≤n}
      zero_mem' := Or.inl rfl
      add_mem' := by intro x y hx hy; change x+y=0 ∨ 2≤x+y; change x=0 ∨ 2≤x at hx; change y=0 ∨ 2≤y at hy; omega }
  conductor := 2
  cofinite _ h := Or.inr h

theorem two_m : two.multiplicity=2 := by
  apply two.multiplicity_eq (by decide) (show 2∈two from Or.inr (by decide))
  intro n hn hp
  change n=0 ∨ 2≤n at hn
  omega

theorem two_atom (n : ℕ) (hn : n=2 ∨ n=3) : two.IsAtom n := by
  refine ⟨Or.inr (by omega),by omega,?_⟩
  intro u hu v hv he
  change u=0 ∨ 2≤u at hu
  change v=0 ∨ 2≤v at hv
  omega

theorem two_e : two.embeddingDimension=2 := by
  have hs : ({2,3}:Finset ℕ) ⊆ two.atoms := by
    intro n hn
    rw [two.mem_atoms_iff]
    apply two_atom
    simpa only [Finset.mem_insert,Finset.mem_singleton] using hn
  have hc := Finset.card_le_card hs
  have hu := two.embeddingDimension_le_multiplicity
  rw [two_m] at hu
  have h2 : 2≤two.embeddingDimension := by
    change 2≤two.atoms.card
    simpa using hc
  omega

noncomputable def atom3 : two.NonXAtom :=
  ⟨⟨3,Or.inr (by decide)⟩,two_atom 3 (Or.inr rfl),by rw [two_m]; decide⟩

example : Fintype.card two.NonXAtom=1 := by rw [two.nonXAtom_card,two_e]
example : Function.Surjective (two.polynomialToA ℚ) := two.polynomialToA_surjective ℚ
example : two.polynomialToG (ZMod 2) (MvPolynomial.X atom3)=two.initialMonomial (ZMod 2) atom3.val := two.polynomialToG_X (ZMod 2) atom3
example : (two.xMultiply ℚ).ker=⊥ := two.xKernel_eq_bot_of_deficit_zero ℚ (by simp [deficit,two_m,two_e])
end PolynomialExamples
