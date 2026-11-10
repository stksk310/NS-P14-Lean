module

public import NSP14.Semigroup.JumpHomogeneity

@[expose] public section

namespace NSP14.NumericalSemigroup

variable (S : NSP14.NumericalSemigroup) (k : Type*) [CommRing k] [Nontrivial k]

omit [Nontrivial k] in
theorem polynomialToG_X_mem_degree (a : S.NonXAtom) :
    S.polynomialToG k (MvPolynomial.X a) ∈ S.tangentDegree k 1 := by
  rw [S.polynomialToG_X]
  exact S.initialMonomial_mem_tangentDegree k 1 a.val (S.atom_order a.property.1)

omit [Nontrivial k] in
theorem polynomialToA_X_mem_degree (a : S.NonXAtom) :
    S.polynomialToA k (MvPolynomial.X a) ∈ S.headDegree k 1 := by
  rw [S.polynomialToA_X]
  exact S.headMonomial_mem_degree k a.val 1 (S.atom_order a.property.1)

theorem polynomialToQ_X_mem_degree (a : S.NonXAtom) :
    S.polynomialToQ k (MvPolynomial.X a) ∈ S.qDegree k 1 := by
  rw [S.polynomialToQ_X]
  exact S.qMonomial_mem_degree k a.val 1 (S.atom_order a.property.1)

omit [Nontrivial k] in
theorem tangentDegree_mul_mem {n p : ℕ} {a b : S.TangentAlgebra k}
    (ha : a ∈ S.tangentDegree k n) (hb : b ∈ S.tangentDegree k p) :
    a*b ∈ S.tangentDegree k (n+p) := by
  obtain ⟨f,rfl⟩ := ha
  obtain ⟨g,rfl⟩ := hb
  exact ⟨S.gradedMul k n p f g,(S.tangent_of_mul k n p f g).symm⟩

omit [Nontrivial k] in
theorem polynomial_X_smul_G_degree (x : S.NonXAtom) (p : ℕ) (a : S.TangentAlgebra k)
    (ha : a ∈ S.tangentDegree k p) :
    (MvPolynomial.X x : S.PolynomialRing k) • a ∈ S.tangentDegree k (1+p) :=
  S.tangentDegree_mul_mem k (S.polynomialToG_X_mem_degree k x) ha

omit [Nontrivial k] in
theorem polynomial_X_smul_T_degree (x : S.NonXAtom) (p : ℕ) (a : (S.xMultiply k).ker)
    (ha : a.val ∈ S.tangentDegree k p) :
    ((MvPolynomial.X x : S.PolynomialRing k) • a).val ∈ S.tangentDegree k (1+p) :=
  S.polynomial_X_smul_G_degree k x p a.val ha

omit [Nontrivial k] in
theorem polynomial_X_smul_A_degree (x : S.NonXAtom) (p : ℕ) (a : S.HeadAlgebra k)
    (ha : a ∈ S.headDegree k p) :
    (MvPolynomial.X x : S.PolynomialRing k) • a ∈ S.headDegree k (1+p) :=
  S.headDegree_mul_mem k (S.polynomialToA_X_mem_degree k x) ha

theorem polynomial_X_smul_N_degree (x : S.NonXAtom) (p : ℕ) (a : (S.nonAperyIdeal k).restrictScalars k)
    (ha : a.val ∈ S.headDegree k p) :
    ((MvPolynomial.X x : S.PolynomialRing k) • a).val ∈ S.headDegree k (1+p) :=
  S.polynomial_X_smul_A_degree k x p a.val ha

theorem polynomial_X_smul_Q_degree (x : S.NonXAtom) (p : ℕ) (a : S.AperyAlgebra k)
    (ha : a ∈ S.qDegree k p) :
    (MvPolynomial.X x : S.PolynomialRing k) • a ∈ S.qDegree k (1+p) :=
  S.qDegree_mul_mem k (S.polynomialToQ_X_mem_degree k x) ha

end NSP14.NumericalSemigroup
