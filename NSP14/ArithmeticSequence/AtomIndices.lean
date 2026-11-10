module
public import NSP14.ArithmeticSequence.HeadIndex
public import NSP14.Semigroup.PolynomialAction
@[expose] public section
open scoped Classical
namespace NSP14.ArithmeticSequence.Data
variable (D : NSP14.ArithmeticSequence.Data)

noncomputable def atomAt (i : Fin (D.v+1)) : D.source.AtomExponent :=
  ⟨⟨D.m+i.val*D.d,D.generator_mem i.val (by have := i.isLt;omega)⟩,
    D.generator_atom i.val (by have := i.isLt;omega)⟩

noncomputable def atomIndexEquiv : Fin (D.v+1) ≃ D.source.AtomExponent :=
  Equiv.ofBijective D.atomAt ⟨by
    intro i j he
    apply Fin.ext
    have hv := congrArg (fun a : D.source.AtomExponent => a.val.val) he
    change D.m+i.val*D.d=D.m+j.val*D.d at hv
    have hd := D.d_pos
    nlinarith,
   by
    intro a
    obtain ⟨i,hi,he⟩ := D.atom_eq_generator a.property
    exact ⟨⟨i,by omega⟩,Subtype.ext (Subtype.ext he.symm)⟩⟩

noncomputable def nonXAtomAt (i : Fin D.v) : D.source.NonXAtom :=
  ⟨⟨D.m+(i.val+1)*D.d,D.generator_mem (i.val+1) (by have := i.isLt;omega)⟩,
    D.generator_atom (i.val+1) (by have := i.isLt;omega),by
      rw [D.multiplicity]
      change D.m+(i.val+1)*D.d≠D.m
      have := D.d_pos
      nlinarith⟩

noncomputable def nonXAtomIndexEquiv : Fin D.v ≃ D.source.NonXAtom :=
  Equiv.ofBijective D.nonXAtomAt ⟨by
    intro i j he
    apply Fin.ext
    have hv := congrArg (fun a : D.source.NonXAtom => a.val.val) he
    change D.m+(i.val+1)*D.d=D.m+(j.val+1)*D.d at hv
    have hd := D.d_pos
    nlinarith,
   by
    intro a
    obtain ⟨i,hi,he⟩ := D.atom_eq_generator a.property.1
    have hp : 1 ≤ i := by
      by_contra hn
      have hz : i=0 := by omega
      have ha := a.property.2
      simp only [hz,Nat.zero_mul,Nat.add_zero] at he
      exact ha (he.trans D.multiplicity.symm)
    refine ⟨⟨i-1,by omega⟩,?_⟩
    apply Subtype.ext
    apply Subtype.ext
    change D.m+(i-1+1)*D.d=a.val.val
    rw [Nat.sub_add_cancel hp]
    exact he.symm⟩

theorem blockCount_one_block {i : ℕ} (hpos : 1 ≤ i) (hupper : i ≤ D.v) : D.blockCount i=1 := by
  have hl := (D.blockCount_le_iff i 1).mpr (by simpa using hupper)
  have hp : 0 < D.blockCount i := by
    have h := D.index_le_blocks i
    by_contra hn
    have hz : D.blockCount i=0 := by omega
    rw [hz,Nat.mul_zero] at h
    omega
  omega

theorem aperyValue_one_block {i : ℕ} (hpos : 1 ≤ i) (hupper : i ≤ D.v) :
    D.aperyValue i=D.m+i*D.d := by
  rw [aperyValue,D.blockCount_one_block hpos hupper,one_mul]

variable (k : Type) [Field k]

theorem nonXAtomIndex_action (i : Fin D.v) :
    D.source.polynomialToA k (MvPolynomial.X (D.nonXAtomIndexEquiv i))=
      D.headIndexMonomial k (i.val+1) := by
  rw [D.source.polynomialToA_X]
  change D.source.headMonomial k (D.nonXAtomAt i).val=D.source.headMonomial k _
  apply congrArg (D.source.headMonomial k)
  apply Subtype.ext
  exact (D.aperyValue_one_block (by omega) (by have := i.isLt;omega)).symm
end NSP14.ArithmeticSequence.Data
