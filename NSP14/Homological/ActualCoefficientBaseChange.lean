module

public import NSP14.Homological.CoordinateBaseChange
public import NSP14.Homological.ActualGrading

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory NSP14.Homological

namespace NSP14.NumericalSemigroup

variable (S : NSP14.NumericalSemigroup) (k : Type) [Field k]

/-- The actual variable matrix has integer 0/1 entries, with the live-order test independent of k. -/
theorem fullG_variable_matrix (x : S.AtomExponent) (i j : S.carrier) :
    S.tangentCoordinates k ((MvPolynomial.X x : S.FullPolynomialRing k) •
      (S.tangentCoordinates k).symm (Finsupp.single i 1)) j =
    if S.order (x.val.val+i.val)=S.order x.val.val+S.order i.val then
      Finsupp.single (x.val+i) (1:k) j else 0 := by
  classical
  have hb : (S.tangentCoordinates k).symm (Finsupp.single i 1)=S.initialMonomial k i := by
    apply (S.tangentCoordinates k).injective
    simp [S.tangentCoordinates_initial]
  rw [hb]
  change S.tangentCoordinates k (S.fullPolynomialToG k (MvPolynomial.X x)*S.initialMonomial k i) j=_
  rw [S.fullPolynomialToG_X]
  by_cases h : S.order (x.val.val+i.val)=S.order x.val.val+S.order i.val
  · rw [ite_eq_left h,S.initialMonomial_mul_live k x.val i h,S.tangentCoordinates_initial]
  · have hz : S.initialMonomial k x.val*S.initialMonomial k i=0 :=
      (S.initialMonomial_mul_eq_zero_iff k x.val i).mpr (by
        have := S.order_add x.val.property i.property
        omega)
    rw [ite_eq_right h,hz,map_zero,Finsupp.zero_apply]

theorem A_variable_matrix_restrict (x : S.NonXAtom) (i j : S.HeadExponent) :
    S.headQuotientEquiv k ((MvPolynomial.X x : S.PolynomialRing k) •
      (S.headQuotientEquiv k).symm (Finsupp.single i 1)) j =
    S.tangentCoordinates k ((MvPolynomial.X (⟨x.val,x.property.1⟩ : S.AtomExponent) : S.FullPolynomialRing k) •
      (S.tangentCoordinates k).symm (Finsupp.single i.val 1)) j.val := by
  have hb : (S.headQuotientEquiv k).symm (Finsupp.single i 1)=S.headMonomial k i.val :=
    (S.headBasis_eq_initial k i)
  have hg : (S.tangentCoordinates k).symm (Finsupp.single i.val 1)=S.initialMonomial k i.val := by
    apply (S.tangentCoordinates k).injective
    simp [S.tangentCoordinates_initial]
  rw [hb,hg]
  change S.headQuotientEquiv k (S.polynomialToA k (MvPolynomial.X x)*S.headMonomial k i.val) j =
    S.tangentCoordinates k (S.fullPolynomialToG k (MvPolynomial.X _)*S.initialMonomial k i.val) j.val
  rw [S.polynomialToA_X,S.fullPolynomialToG_X]
  change S.headQuotientEquiv k (Ideal.Quotient.mk _ (S.initialMonomial k x.val*S.initialMonomial k i.val)) j = _
  rw [S.headQuotientEquiv_mk]
  rfl

theorem T_variable_matrix_restrict (x : S.NonXAtom) (i j : S.TerminalExponent) :
    S.xKernelEquiv k ((MvPolynomial.X x : S.PolynomialRing k) •
      (S.xKernelEquiv k).symm (Finsupp.single i 1)) j =
    S.tangentCoordinates k ((MvPolynomial.X (⟨x.val,x.property.1⟩ : S.AtomExponent) : S.FullPolynomialRing k) •
      (S.tangentCoordinates k).symm (Finsupp.single i.val 1)) j.val := by
  have hb : (S.xKernelEquiv k).symm (Finsupp.single i 1)=S.terminalMonomial k i := by
    apply (S.xKernelEquiv k).injective
    rw [LinearEquiv.apply_symm_apply,S.xKernelEquiv_terminal]
  have hg : (S.tangentCoordinates k).symm (Finsupp.single i.val 1)=S.initialMonomial k i.val := by
    apply (S.tangentCoordinates k).injective
    simp [S.tangentCoordinates_initial]
  rw [hb,hg]
  change S.tangentCoordinates k (S.polynomialToG k (MvPolynomial.X x)*S.initialMonomial k i.val) j.val =
    S.tangentCoordinates k (S.fullPolynomialToG k (MvPolynomial.X _)*S.initialMonomial k i.val) j.val
  rw [S.polynomialToG_X,S.fullPolynomialToG_X]

theorem N_variable_matrix_restrict (x : S.NonXAtom) (i j : S.NonAperyHeadExponent) :
    S.nonAperyIdealEquiv k ((MvPolynomial.X x : S.PolynomialRing k) •
      (S.nonAperyIdealEquiv k).symm (Finsupp.single i 1)) j =
    S.headQuotientEquiv k ((MvPolynomial.X x : S.PolynomialRing k) •
      (S.headQuotientEquiv k).symm (Finsupp.single i.val 1)) j.val := by
  have hb : (S.nonAperyIdealEquiv k).symm (Finsupp.single i 1)=S.nonAperyMonomial k i := by
    apply (S.nonAperyIdealEquiv k).injective
    rw [LinearEquiv.apply_symm_apply,S.nonAperyIdealEquiv_initial]
  rw [hb]
  change S.headQuotientEquiv k (S.polynomialToA k (MvPolynomial.X x)*S.headMonomial k i.val.val) j.val = _
  rw [show (S.headQuotientEquiv k).symm (Finsupp.single i.val 1)=S.headMonomial k i.val.val from
    S.headBasis_eq_initial k i.val]
  rfl

theorem Q_variable_matrix_restrict (x : S.NonXAtom) (i j : S.AperyExponent) :
    S.aperyQuotientEquiv k ((MvPolynomial.X x : S.PolynomialRing k) •
      (S.aperyQuotientEquiv k).symm (Finsupp.single i 1)) j =
    S.tangentCoordinates k ((MvPolynomial.X (⟨x.val,x.property.1⟩ : S.AtomExponent) : S.FullPolynomialRing k) •
      (S.tangentCoordinates k).symm (Finsupp.single i.val 1)) j.val := by
  have hb : (S.aperyQuotientEquiv k).symm (Finsupp.single i 1)=S.qMonomial k i.val := by
    apply (S.aperyQuotientEquiv k).injective
    rw [LinearEquiv.apply_symm_apply,S.aperyQuotientEquiv_initial]
  have hg : (S.tangentCoordinates k).symm (Finsupp.single i.val 1)=S.initialMonomial k i.val := by
    apply (S.tangentCoordinates k).injective
    simp [S.tangentCoordinates_initial]
  rw [hb,hg]
  change S.aperyQuotientEquiv k (S.polynomialToQ k (MvPolynomial.X x)*S.qMonomial k i.val) j =
    S.tangentCoordinates k (S.fullPolynomialToG k (MvPolynomial.X _)*S.initialMonomial k i.val) j.val
  rw [S.polynomialToQ_X,S.fullPolynomialToG_X]
  change S.aperyQuotientEquiv k (S.toAperyAlgebra k (S.initialMonomial k x.val*S.initialMonomial k i.val)) j = _
  rw [S.toAperyAlgebra_coordinates]

variable (L : Type) [Field L] [Algebra k L]

theorem fullG_variable_matrix_baseChange (x : S.AtomExponent) (i j : S.carrier) :
    S.tangentCoordinates L ((MvPolynomial.X x : S.FullPolynomialRing L) •
      (S.tangentCoordinates L).symm (Finsupp.single i 1)) j =
        algebraMap k L (S.tangentCoordinates k ((MvPolynomial.X x : S.FullPolynomialRing k) •
          (S.tangentCoordinates k).symm (Finsupp.single i 1)) j) := by
  classical
  rw [S.fullG_variable_matrix L,S.fullG_variable_matrix k]
  split_ifs <;> by_cases hij : x.val+i=j <;> simp [hij]

/-- Scalar extension of algebraic actual G is actual G with coefficient field L.
No statement about tensoring the entire formal power-series ring is used. -/
noncomputable def fullG_baseChangeIso :
    polynomialBaseChangeModule k L S.AtomExponent
      (ModuleCat.of (S.FullPolynomialRing k) (S.TangentAlgebra k)) ≅
        ModuleCat.of (S.FullPolynomialRing L) (S.TangentAlgebra L) :=
  coordinateBaseChangePolynomialIso k L S.AtomExponent S.carrier _ _
    ((coefficientOriginalEquiv k S.AtomExponent (S.TangentAlgebra k)).trans (S.tangentCoordinates k))
    ((coefficientOriginalEquiv L S.AtomExponent (S.TangentAlgebra L)).trans (S.tangentCoordinates L)) (by
      intro x i j
      change S.tangentCoordinates L ((MvPolynomial.X x : S.FullPolynomialRing L) •
        (S.tangentCoordinates L).symm (Finsupp.single i 1)) j =
        algebraMap k L (S.tangentCoordinates k ((MvPolynomial.X x : S.FullPolynomialRing k) •
          (S.tangentCoordinates k).symm (Finsupp.single i 1)) j)
      rw [S.fullG_variable_matrix L,S.fullG_variable_matrix k]
      split_ifs <;> by_cases hij : x.val+i=j <;> simp [hij])

/-- Actual coefficient extension for T, in its inherited non-x polynomial action. -/
noncomputable def actualT_baseChangeIso :
    polynomialBaseChangeModule k L S.NonXAtom
      (ModuleCat.of (S.PolynomialRing k) ((S.xMultiply k).ker)) ≅
        ModuleCat.of (S.PolynomialRing L) ((S.xMultiply L).ker) :=
  coordinateBaseChangePolynomialIso k L S.NonXAtom (S.TerminalExponent) _ _
    ((coefficientOriginalEquiv k S.NonXAtom ((S.xMultiply k).ker)).trans (S.xKernelEquiv k))
    ((coefficientOriginalEquiv L S.NonXAtom ((S.xMultiply L).ker)).trans (S.xKernelEquiv L)) (by
      intro x i j
      change (S.xKernelEquiv L) ((MvPolynomial.X x : S.PolynomialRing L) •
        (S.xKernelEquiv L).symm (Finsupp.single i 1)) j =
        algebraMap k L ((S.xKernelEquiv k) ((MvPolynomial.X x : S.PolynomialRing k) •
          (S.xKernelEquiv k).symm (Finsupp.single i 1)) j)
      rw [S.T_variable_matrix_restrict L,S.T_variable_matrix_restrict k]
      exact S.fullG_variable_matrix_baseChange k L _ _ _)

/-- Actual coefficient extension for A, in its inherited non-x polynomial action. -/
noncomputable def actualA_baseChangeIso :
    polynomialBaseChangeModule k L S.NonXAtom
      (ModuleCat.of (S.PolynomialRing k) (S.HeadAlgebra k)) ≅
        ModuleCat.of (S.PolynomialRing L) (S.HeadAlgebra L) :=
  coordinateBaseChangePolynomialIso k L S.NonXAtom (S.HeadExponent) _ _
    ((coefficientOriginalEquiv k S.NonXAtom (S.HeadAlgebra k)).trans (S.headQuotientEquiv k))
    ((coefficientOriginalEquiv L S.NonXAtom (S.HeadAlgebra L)).trans (S.headQuotientEquiv L)) (by
      intro x i j
      change (S.headQuotientEquiv L) ((MvPolynomial.X x : S.PolynomialRing L) •
        (S.headQuotientEquiv L).symm (Finsupp.single i 1)) j =
        algebraMap k L ((S.headQuotientEquiv k) ((MvPolynomial.X x : S.PolynomialRing k) •
          (S.headQuotientEquiv k).symm (Finsupp.single i 1)) j)
      rw [S.A_variable_matrix_restrict L,S.A_variable_matrix_restrict k]
      exact S.fullG_variable_matrix_baseChange k L _ _ _)

/-- Actual coefficient extension for N, in its inherited non-x polynomial action. -/
noncomputable def actualN_baseChangeIso :
    polynomialBaseChangeModule k L S.NonXAtom
      (ModuleCat.of (S.PolynomialRing k) (((S.nonAperyIdeal k).restrictScalars k))) ≅
        ModuleCat.of (S.PolynomialRing L) (((S.nonAperyIdeal L).restrictScalars L)) :=
  coordinateBaseChangePolynomialIso k L S.NonXAtom (S.NonAperyHeadExponent) _ _
    ((coefficientOriginalEquiv k S.NonXAtom (((S.nonAperyIdeal k).restrictScalars k))).trans (S.nonAperyIdealEquiv k))
    ((coefficientOriginalEquiv L S.NonXAtom (((S.nonAperyIdeal L).restrictScalars L))).trans (S.nonAperyIdealEquiv L)) (by
      intro x i j
      change (S.nonAperyIdealEquiv L) ((MvPolynomial.X x : S.PolynomialRing L) •
        (S.nonAperyIdealEquiv L).symm (Finsupp.single i 1)) j =
        algebraMap k L ((S.nonAperyIdealEquiv k) ((MvPolynomial.X x : S.PolynomialRing k) •
          (S.nonAperyIdealEquiv k).symm (Finsupp.single i 1)) j)
      rw [S.N_variable_matrix_restrict L,S.N_variable_matrix_restrict k]
      rw [S.A_variable_matrix_restrict L,S.A_variable_matrix_restrict k]
      exact S.fullG_variable_matrix_baseChange k L _ _ _)

/-- Actual coefficient extension for Q, in its inherited non-x polynomial action. -/
noncomputable def actualQ_baseChangeIso :
    polynomialBaseChangeModule k L S.NonXAtom
      (ModuleCat.of (S.PolynomialRing k) (S.AperyAlgebra k)) ≅
        ModuleCat.of (S.PolynomialRing L) (S.AperyAlgebra L) :=
  coordinateBaseChangePolynomialIso k L S.NonXAtom (S.AperyExponent) _ _
    ((coefficientOriginalEquiv k S.NonXAtom (S.AperyAlgebra k)).trans (S.aperyQuotientEquiv k))
    ((coefficientOriginalEquiv L S.NonXAtom (S.AperyAlgebra L)).trans (S.aperyQuotientEquiv L)) (by
      intro x i j
      change (S.aperyQuotientEquiv L) ((MvPolynomial.X x : S.PolynomialRing L) •
        (S.aperyQuotientEquiv L).symm (Finsupp.single i 1)) j =
        algebraMap k L ((S.aperyQuotientEquiv k) ((MvPolynomial.X x : S.PolynomialRing k) •
          (S.aperyQuotientEquiv k).symm (Finsupp.single i 1)) j)
      rw [S.Q_variable_matrix_restrict L,S.Q_variable_matrix_restrict k]
      exact S.fullG_variable_matrix_baseChange k L _ _ _)

theorem actualG_totalBetti_baseChange (i : ℕ) :
    totalBetti L S.AtomExponent (ModuleCat.of (S.FullPolynomialRing L) (S.TangentAlgebra L)) i =
      totalBetti k S.AtomExponent (ModuleCat.of (S.FullPolynomialRing k) (S.TangentAlgebra k)) i :=
  (totalBetti_iso L S.AtomExponent (S.fullG_baseChangeIso k L) i).symm.trans
    (totalBetti_baseChange k L S.AtomExponent _ i)

theorem actualT_totalBetti_baseChange (i : ℕ) :
    totalBetti L S.NonXAtom (ModuleCat.of (S.PolynomialRing L) ((S.xMultiply L).ker)) i =
      totalBetti k S.NonXAtom (ModuleCat.of (S.PolynomialRing k) ((S.xMultiply k).ker)) i :=
  (totalBetti_iso L S.NonXAtom (S.actualT_baseChangeIso k L) i).symm.trans
    (totalBetti_baseChange k L S.NonXAtom _ i)

theorem actualA_totalBetti_baseChange (i : ℕ) :
    totalBetti L S.NonXAtom (ModuleCat.of (S.PolynomialRing L) (S.HeadAlgebra L)) i =
      totalBetti k S.NonXAtom (ModuleCat.of (S.PolynomialRing k) (S.HeadAlgebra k)) i :=
  (totalBetti_iso L S.NonXAtom (S.actualA_baseChangeIso k L) i).symm.trans
    (totalBetti_baseChange k L S.NonXAtom _ i)

theorem actualN_totalBetti_baseChange (i : ℕ) :
    totalBetti L S.NonXAtom (ModuleCat.of (S.PolynomialRing L) (((S.nonAperyIdeal L).restrictScalars L))) i =
      totalBetti k S.NonXAtom (ModuleCat.of (S.PolynomialRing k) (((S.nonAperyIdeal k).restrictScalars k))) i :=
  (totalBetti_iso L S.NonXAtom (S.actualN_baseChangeIso k L) i).symm.trans
    (totalBetti_baseChange k L S.NonXAtom _ i)

theorem actualQ_totalBetti_baseChange (i : ℕ) :
    totalBetti L S.NonXAtom (ModuleCat.of (S.PolynomialRing L) (S.AperyAlgebra L)) i =
      totalBetti k S.NonXAtom (ModuleCat.of (S.PolynomialRing k) (S.AperyAlgebra k)) i :=
  (totalBetti_iso L S.NonXAtom (S.actualQ_baseChangeIso k L) i).symm.trans
    (totalBetti_baseChange k L S.NonXAtom _ i)

end NSP14.NumericalSemigroup
