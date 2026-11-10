module
public import NSP14.ArithmeticSequence.ModelNativeWindow
public import NSP14.ArithmeticSequence.WindowArithmetic
public import NSP14.ArithmeticSequence.AtomIndices
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory NSP14.Homological
open scoped Classical
namespace NSP14.ArithmeticSequence.Data
variable (D : NSP14.ArithmeticSequence.Data) (hv : 2 ≤ D.v) (k : Type) [Field k]

noncomputable def modelWindowClass (n : ℕ) : D.modelNativeQuotient hv k :=
  Submodule.Quotient.mk (D.modelKernelNatBasis hv k n)

theorem modelWindowClass_coordinates (n : ℕ) :
    D.modelNativeWindowEquiv hv k (D.modelWindowClass hv k n)=
      (fun a : Fin D.v => if n=a.val then 1 else 0) := by
  rw [modelWindowClass,D.modelNativeWindowEquiv_mk]
  simp only [Module.Basis.repr_self,Finsupp.single_apply]

theorem modelWindowClass_zero {n : ℕ} (hn : D.v ≤ n) : D.modelWindowClass hv k n=0 := by
  apply (D.modelNativeWindowEquiv hv k).injective
  rw [D.modelWindowClass_coordinates,map_zero]
  funext a
  rw [ite_eq_right (by have ha:=a.isLt;omega)]
  rfl

theorem modelKernelMonomial_mul (i : {i : ℕ // D.m ≤ i}) (j : ℕ) :
    D.modelMonomial hv k j • D.modelKernelMonomial hv k i=
      if D.blockCount (i.val+j)=D.blockCount i.val+D.blockCount j
      then D.modelKernelMonomial hv k ⟨i.val+j,by omega⟩ else 0 := by
  apply Subtype.ext
  change D.modelMonomial hv k j*D.modelMonomial hv k i.val=_
  rw [mul_comm,D.modelMonomial_mul]
  split_ifs <;> rfl

theorem modelWindowClass_action (n j : ℕ) :
    D.modelMonomial hv k j • D.modelWindowClass hv k n=
      if D.blockCount (D.m+n+j)=D.blockCount (D.m+n)+D.blockCount j
      then D.modelWindowClass hv k (n+j) else 0 := by
  change Submodule.Quotient.mk (D.modelMonomial hv k j • D.modelKernelNatBasis hv k n)=_
  rw [D.modelKernelNatBasis_monomial,D.modelKernelMonomial_mul]
  split_ifs with h
  · change Submodule.Quotient.mk (D.modelKernelMonomial hv k ⟨D.m+n+j,by omega⟩)=_
    rw [modelWindowClass,D.modelKernelNatBasis_monomial]
    congr 2
    apply Subtype.ext
    exact Nat.add_assoc _ _ _
  · rfl

/-- The window action has exactly two degrees: a variable takes a lower
coordinate to an upper coordinate, and kills every other coordinate. -/
theorem modelWindowClass_twoStep (n j : ℕ) (hn : n < D.v) (hj : 1 ≤ j) (hjv : j ≤ D.v) :
    D.modelMonomial hv k j • D.modelWindowClass hv k n=
      if n<D.residueDefect ∧ D.residueDefect≤n+j ∧ n+j<D.v
      then D.modelWindowClass hv k (n+j) else 0 := by
  rw [D.modelWindowClass_action]
  by_cases hnj : n+j<D.v
  · rw [Nat.add_assoc D.m n j,D.window_blockCount (n+j) hnj,D.window_blockCount n hn,
      D.blockCount_one_block hj hjv]
    have he : ((D.m-1)/D.v+(if n+j<D.residueDefect then 1 else 2)=
        (D.m-1)/D.v+(if n<D.residueDefect then 1 else 2)+1) ↔
        (n<D.residueDefect ∧ D.residueDefect≤n+j ∧ n+j<D.v) := by
      by_cases hl : n<D.residueDefect <;> by_cases hu : n+j<D.residueDefect <;>
        simp [hl,hu,hnj]; omega
    simp only [he]
  · have hz := D.modelWindowClass_zero hv k (show D.v ≤ n+j by omega)
    rw [hz]
    simp only [ite_self,hnj,and_false]
end NSP14.ArithmeticSequence.Data
