module

public import NSP14.Homological.CoordinateGrading
public import NSP14.Homological.PresentationGrading
public import NSP14.Homological.GradedBetti

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open NSP14.Homological

namespace NSP14.NumericalSemigroup

variable (S : NSP14.NumericalSemigroup) (k : Type) [Field k]

/-- The full e-variable grading is the existing ideal-power grading of actual G. -/
noncomputable def fullGGrading : GradedPolynomialModule k S.AtomExponent
    (ModuleCat.of (S.FullPolynomialRing k) (S.TangentAlgebra k)) :=
  actualCoordinateGrading k S.carrier S.AtomExponent (S.TangentAlgebra k)
    (fun t => S.order t.val) (S.tangentCoordinates k) (S.tangentDegree k)
    (fun p a => by rw [S.mem_tangentDegree_coordinates,Finsupp.mem_supported'];rfl)
    (fun x p a ha => by
      change S.fullPolynomialToG k (MvPolynomial.X x) * a∈_
      rw [S.fullPolynomialToG_X]
      simpa only [Nat.add_comm 1 p] using S.tangentDegree_mul_mem k
        (S.initialMonomial_mem_tangentDegree k 1 x.val (S.atom_order x.property)) ha)

noncomputable def nonXGGrading : GradedPolynomialModule k S.NonXAtom
    (ModuleCat.of (S.PolynomialRing k) (S.TangentAlgebra k)) :=
  actualCoordinateGrading k S.carrier S.NonXAtom (S.TangentAlgebra k)
    (fun t => S.order t.val) (S.tangentCoordinates k) (S.tangentDegree k)
    (fun p a => by rw [S.mem_tangentDegree_coordinates,Finsupp.mem_supported'];rfl)
    (fun x p a ha => by simpa only [Nat.add_comm 1 p] using S.polynomial_X_smul_G_degree k x p a ha)

noncomputable def actualAGrading : GradedPolynomialModule k S.NonXAtom
    (ModuleCat.of (S.PolynomialRing k) (S.HeadAlgebra k)) :=
  actualCoordinateGrading k S.HeadExponent S.NonXAtom (S.HeadAlgebra k)
    (fun t => S.order t.val.val) (S.headQuotientEquiv k) (S.headDegree k)
    (fun p a => by rw [S.mem_headDegree_coordinates,Finsupp.mem_supported'];rfl)
    (fun x p a ha => by simpa only [Nat.add_comm 1 p] using S.polynomial_X_smul_A_degree k x p a ha)

noncomputable def actualQGrading : GradedPolynomialModule k S.NonXAtom
    (ModuleCat.of (S.PolynomialRing k) (S.AperyAlgebra k)) :=
  actualCoordinateGrading k S.AperyExponent S.NonXAtom (S.AperyAlgebra k)
    (fun t => S.order t.val.val) (S.aperyQuotientEquiv k) (S.qDegree k)
    (fun p a => by rw [S.mem_qDegree_coordinates,Finsupp.mem_supported'];rfl)
    (fun x p a ha => by simpa only [Nat.add_comm 1 p] using S.polynomial_X_smul_Q_degree k x p a ha)

theorem terminalDegree_coordinates (p : ℕ) (a : (S.xMultiply k).ker) :
    a.val∈S.tangentDegree k p ↔
      ∀ t : S.TerminalExponent,S.order t.val.val≠p → S.xKernelEquiv k a t=0 := by
  classical
  rw [S.mem_tangentDegree_coordinates,Finsupp.mem_supported']
  constructor
  · intro h t ht
    exact h t.val ht
  · intro h t ht
    by_cases hterm : S.Terminal t.val
    · exact h ⟨t,hterm⟩ ht
    · have ha := (S.mem_xKernel_coordinates k a.val).mp a.property
      rw [S.coordinateShift_ker,Finsupp.mem_supported'] at ha
      exact ha t hterm

noncomputable def actualTGrading : GradedPolynomialModule k S.NonXAtom
    (ModuleCat.of (S.PolynomialRing k) (S.xMultiply k).ker) :=
  actualCoordinateGrading k S.TerminalExponent S.NonXAtom (S.xMultiply k).ker
    (fun t => S.order t.val.val) (S.xKernelEquiv k)
    (fun p => (S.tangentDegree k p).comap (S.xMultiply k).ker.subtype)
    (S.terminalDegree_coordinates k)
    (fun x p a ha => by
      change ((MvPolynomial.X x : S.PolynomialRing k) • a).val∈S.tangentDegree k (p+1)
      simpa only [Nat.add_comm 1 p] using S.polynomial_X_smul_T_degree k x p a ha)

theorem nonAperyDegree_coordinates (p : ℕ) (a : (S.nonAperyIdeal k).restrictScalars k) :
    a.val∈S.headDegree k p ↔
      ∀ t : S.NonAperyHeadExponent,S.order t.val.val.val≠p → S.nonAperyIdealEquiv k a t=0 := by
  classical
  rw [S.mem_headDegree_coordinates,Finsupp.mem_supported']
  constructor
  · intro h t ht
    exact h t.val ht
  · intro h t ht
    by_cases hn : t.val.val∉S.aperySet
    · exact h ⟨t,hn⟩ ht
    · exact (Finsupp.mem_supported' k _).mp a.property t hn

noncomputable def actualNGrading : GradedPolynomialModule k S.NonXAtom
    (ModuleCat.of (S.PolynomialRing k) ((S.nonAperyIdeal k).restrictScalars k)) :=
  actualCoordinateGrading k S.NonAperyHeadExponent S.NonXAtom ((S.nonAperyIdeal k).restrictScalars k)
    (fun t => S.order t.val.val.val) (S.nonAperyIdealEquiv k)
    (fun p => (S.headDegree k p).comap ((S.nonAperyIdeal k).restrictScalars k).subtype)
    (S.nonAperyDegree_coordinates k)
    (fun x p a ha => by
      change ((MvPolynomial.X x : S.PolynomialRing k) • a).val∈S.headDegree k (p+1)
      simpa only [Nat.add_comm 1 p] using S.polynomial_X_smul_N_degree k x p a ha)

theorem descendingStratum_X_degree (s p : ℕ) (x : S.NonXAtom)
    (a : S.DescendingJumpStratum k s) (ha : a∈S.descendingStratumDegree k s p) :
    (MvPolynomial.X x : S.PolynomialRing k) • a∈S.descendingStratumDegree k s (p+1) := by
  obtain ⟨b,hb,rfl⟩ := ha
  refine ⟨(MvPolynomial.X x : S.PolynomialRing k) • b,?_,rfl⟩
  change (((MvPolynomial.X x : S.PolynomialRing k) • b).val).val∈S.tangentDegree k (p+1)
  simpa only [Nat.add_comm 1 p,Submodule.coe_smul] using S.polynomial_X_smul_T_degree k x p b.val hb

theorem ascendingStratum_X_degree (s p : ℕ) (x : S.NonXAtom)
    (a : S.AscendingJumpStratum k s) (ha : a∈S.ascendingStratumDegree k s p) :
    (MvPolynomial.X x : S.PolynomialRing k) • a∈S.ascendingStratumDegree k s (p+1) := by
  obtain ⟨b,hb,rfl⟩ := ha
  refine ⟨(MvPolynomial.X x : S.PolynomialRing k) • b,?_,rfl⟩
  change (((MvPolynomial.X x : S.PolynomialRing k) • b).val).val∈S.headDegree k (p+1)
  simpa only [Nat.add_comm 1 p,Submodule.coe_smul] using S.polynomial_X_smul_N_degree k x p b.val hb

noncomputable def descendingStratumGrading (s : ℕ) : GradedPolynomialModule k S.NonXAtom
    (ModuleCat.of (S.PolynomialRing k) (S.DescendingJumpStratum k s)) :=
  actualCoordinateGrading k (S.JumpExponent s) S.NonXAtom (S.DescendingJumpStratum k s)
    (fun t => S.order t.val.val.val) (S.descendingStratumCoordinates k s) (S.descendingStratumDegree k s)
    (fun p a => by rw [S.descendingStratumDegree_coordinates];exact Finsupp.mem_supported' k _)
    (fun x p a ha => S.descendingStratum_X_degree k s p x a ha)

noncomputable def ascendingStratumGrading (s : ℕ) (hs : 0<s) : GradedPolynomialModule k S.NonXAtom
    (ModuleCat.of (S.PolynomialRing k) (S.AscendingJumpStratum k s)) :=
  actualCoordinateGrading k (S.JumpExponent s) S.NonXAtom (S.AscendingJumpStratum k s)
    (fun t => S.order (S.terminalHeadExponentEquiv t.val).val.val.val)
    (S.ascendingStratumCoordinates k s hs) (S.ascendingStratumDegree k s)
    (fun p a => by rw [S.ascendingStratumDegree_coordinates k s p hs];exact Finsupp.mem_supported' k _)
    (fun x p a ha => S.ascendingStratum_X_degree k s p x a ha)

end NSP14.NumericalSemigroup
