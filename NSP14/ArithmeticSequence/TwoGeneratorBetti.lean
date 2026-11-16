module
public import NSP14.ArithmeticSequence.ConeRegular
public import NSP14.Semigroup.RegularHeadBetti
public import NSP14.Semigroup.AugmentationBetti
public import NSP14.Homological.FiniteKoszulEulerAbove
@[expose] public section
open NSP14.Homological
namespace NSP14.ArithmeticSequence.Data
variable (D : ArithmeticSequence.Data)

theorem nonXAtom_card : Fintype.card D.source.NonXAtom=D.v := by
  rw [D.source.nonXAtom_card,D.embeddingDimension,Nat.add_sub_cancel]

variable (k : Type) [Field k]

theorem twoGenerator_cone_betti_one (hv : D.v=1) :
    totalBetti k D.source.AtomExponent (ModuleCat.of (D.source.FullPolynomialRing k) (D.source.TangentAlgebra k)) 1=1 := by
  have ht := finite_koszul_bettiEuler_eq_zero_of_ge k D.source.NonXAtom (D.source.headPolynomialModule k)
    (by rw [D.nonXAtom_card,hv]) 1 (by rw [D.nonXAtom_card,hv])
  have hb := bettiEuler_succ k D.source.NonXAtom (D.source.headPolynomialModule k) 0
  rw [bettiEuler_zero,D.source.actualA_totalBetti_zero k,ht] at hb
  rw [D.source.xRegular_totalBetti k (D.xMultiply_injective k)]
  change (0 : ℤ)=(totalBetti k D.source.NonXAtom (D.source.headPolynomialModule k) 1 : ℤ)-1 at hb
  have h1 : (totalBetti k D.source.NonXAtom (D.source.headPolynomialModule k) 1 : ℤ)=1 := by linarith [hb]
  exact_mod_cast h1

theorem twoGenerator_cone_betti_above (hv : D.v=1) (i : ℕ) (hi : 1 < i) :
    totalBetti k D.source.AtomExponent (ModuleCat.of (D.source.FullPolynomialRing k) (D.source.TangentAlgebra k)) i=0 := by
  rw [D.source.xRegular_totalBetti k (D.xMultiply_injective k)]
  exact totalBetti_eq_zero_of_gt k D.source.NonXAtom (D.source.headPolynomialModule k) i (by rw [D.nonXAtom_card,hv];exact hi)
end NSP14.ArithmeticSequence.Data
