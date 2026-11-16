module
public import NSP14.ArithmeticSequence.AtomIndices
public import NSP14.ArithmeticSequence.WindowPolynomialModule
public import NSP14.Semigroup.AtomVariableOrder
@[expose] public section
open scoped Classical
open CategoryTheory NSP14.Homological
namespace NSP14.ArithmeticSequence.Data
variable (D : NSP14.ArithmeticSequence.Data) (hv : 2 ≤ D.v)

theorem modelExponent_oneBlock {j : ℕ} (hj : 1 ≤ j) (hjv : j ≤ D.v) :
    D.modelExponent j=D.v+(D.v-j) := by
  rw [modelExponent,D.blockCount_one_block hj hjv]
  omega

noncomputable def modelFullAtomAt (i : Fin D.v) : (D.ordinaryModel hv).source.AtomExponent :=
  ⟨⟨D.modelExponent (i.val+1),D.modelExponent_mem hv _⟩,by
    have h := (D.ordinaryModel hv).generator_atom (D.v-(i.val+1)) (by
      change D.v-(i.val+1) ≤ D.v-1
      have := i.isLt
      omega)
    change (D.ordinaryModel hv).source.IsAtom (D.modelExponent (i.val+1))
    rw [D.modelExponent_oneBlock (by omega) (by have := i.isLt;omega)]
    simpa only [ordinaryModel,Nat.mul_one] using h⟩

noncomputable def modelFullAtomEquiv : Fin D.v ≃ (D.ordinaryModel hv).source.AtomExponent :=
  Equiv.ofBijective (D.modelFullAtomAt hv) ⟨by
    intro i j he
    have h := D.modelExponent_injective (congrArg (fun a : (D.ordinaryModel hv).source.AtomExponent => a.val.val) he)
    apply Fin.ext
    omega,
   by
    intro a
    obtain ⟨j,hj,he⟩ := (D.ordinaryModel hv).atom_eq_generator a.property
    change j ≤ D.v-1 at hj
    change a.val.val=D.v+j*1 at he
    let i : Fin D.v := ⟨D.v-1-j,by omega⟩
    refine ⟨i,?_⟩
    apply Subtype.ext
    apply Subtype.ext
    change D.modelExponent (i.val+1)=a.val.val
    rw [D.modelExponent_oneBlock (by omega) (by dsimp [i];omega),he,Nat.mul_one]
    dsimp [i]
    omega⟩

theorem modelFullAtomEquiv_value (i : Fin D.v) :
    (D.modelFullAtomEquiv hv i).val.val=D.modelExponent (i.val+1) := rfl

variable (k : Type) [Field k]

noncomputable def modelFullPolynomial :
    VariableRing k (Fin D.v) →ₐ[k] (D.ordinaryModel hv).source.TangentAlgebra k :=
  MvPolynomial.aeval (fun i => D.modelMonomial hv k (i.val+1))

theorem modelFullPolynomial_X (i : Fin D.v) :
    D.modelFullPolynomial hv k (MvPolynomial.X i)=D.modelMonomial hv k (i.val+1) :=
  MvPolynomial.aeval_X _ i

theorem modelAtomPolynomial_X (i : Fin D.v) :
    (D.ordinaryModel hv).source.fullPolynomialToG k (MvPolynomial.X (D.modelFullAtomEquiv hv i))=
      D.modelFullPolynomial hv k (MvPolynomial.X i) := by
  rw [(D.ordinaryModel hv).source.fullPolynomialToG_X,D.modelFullPolynomial_X]
  rfl
end NSP14.ArithmeticSequence.Data
