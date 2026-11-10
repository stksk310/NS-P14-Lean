module
public import NSP14.ArithmeticSequence.ModelHeadBetti
public import NSP14.ArithmeticSequence.ModelKernelDivision
public import NSP14.Homological.KoszulVariableMaps
public import NSP14.Homological.QuotientBettiAdditivity
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits HomologicalComplex NSP14.Homological
namespace NSP14.ArithmeticSequence.Data
variable (D : NSP14.ArithmeticSequence.Data) (hv : 2 ≤ D.v) (k : Type) [Field k]

/-- The actual Tor map of the actual inclusion J→B vanishes in every
row because it factors through multiplication by the actual x variable. -/
theorem modelKernelFull_homology_zero (i : ℕ) :
    homologyMap ((coefficientKoszulFunctor k (Fin D.v)).map (D.modelFullSequence hv k).f) i=0 := by
  change homologyMap ((coefficientKoszulFunctor k (Fin D.v)).map (D.modelKernelFullInclusion hv k)) i=0
  rw [D.modelKernelFullInclusion_factor]
  exact coefficientKoszulHomology_map_variable_multiple k (Fin D.v)
    (D.modelKernelFullDivision hv k) ⟨D.v-1,by omega⟩ i

/-- Exact LES additivity for the actual quotient. No vanishing map or
spectral degeneration is an input. -/
theorem modelHeadFull_betti_add (i : ℕ) :
    totalBetti k (Fin D.v) (D.modelHeadFull hv k) (i+1)=
      totalBetti k (Fin D.v) (D.modelRegularFull hv k) (i+1)+
        totalBetti k (Fin D.v) (D.modelKernelFull hv k) i := by
  let : Module.Finite (VariableRing k (Fin D.v)) (D.modelFullSequence hv k).X₁ := D.modelKernelFullFinite hv k
  let : Module.Finite (VariableRing k (Fin D.v)) (D.modelFullSequence hv k).X₂ := D.modelRegularFullFinite hv k
  let : Module.Finite (VariableRing k (Fin D.v)) (D.modelFullSequence hv k).X₃ := D.modelHeadFullFinite hv k
  exact koszul_quotient_betti_additivity k (Fin D.v) (D.modelFullSequence hv k)
    (D.modelFullSequence_shortExact hv k) i (D.modelKernelFull_homology_zero hv k)

include hv in
/-- The full actual AP cone table over every infinite field. -/
theorem apCone_betti_infinite [Infinite k] (i : ℕ) (hi : 1 ≤ i) :
    totalBetti k D.source.AtomExponent
      (ModuleCat.of (D.source.FullPolynomialRing k) (D.source.TangentAlgebra k)) i=
      i*D.v.choose (i+1)+
        (if i≤D.residueDefect then (D.residueDefect+1-i)*D.v.choose (i-1)
         else (i-D.residueDefect)*D.v.choose i) := by
  rw [D.apCone_betti_eq_modelHead hv k]
  cases i with
  | zero => omega
  | succ j =>
    rw [D.modelHeadFull_betti_add,D.modelRegularFull_betti_pos hv k (j+1) (by omega),D.modelKernelFull_betti]
    have he : D.residueDefect-j=D.residueDefect+1-(j+1) := by omega
    simp only [Nat.add_sub_cancel,he]
end NSP14.ArithmeticSequence.Data
