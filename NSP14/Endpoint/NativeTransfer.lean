module
public import NSP14.Endpoint.VariableOrder
public import NSP14.Endpoint.H0Internal
public import NSP14.Homological.RegularCorrectedComparison
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open scoped Classical BigOperators
open CategoryTheory HomologicalComplex NSP14.Homological
namespace NSP14.Endpoint.Data
variable (D : NSP14.Endpoint.Data) (k : Type) [Field k]

noncomputable def fullRegularIso :
    polynomialRegularModule k D.Variables (D.source.TangentAlgebra k) (D.fullToG k) ≅ D.fullG k := by
  let e : polynomialRegularModule k D.Variables (D.source.TangentAlgebra k) (D.fullToG k) ≃ₗ[D.FullRing k] D.fullG k :=
    {toFun a := a
     invFun a := a
     left_inv _ := rfl
     right_inv _ := rfl
     map_add' _ _ := rfl
     map_smul' _ _ := rfl}
  exact e.toModuleIso

noncomputable def endpointExtendedComplex : ChainComplex (ModuleCat k) ℕ :=
  regularExtendedCoefficientComplex k (D.source.TangentAlgebra k) D.a
    (D.endpointElements k) (D.internalToG k) (D.internalVariableList k)

theorem endpointExtended_betti (i : ℕ) :
    Module.finrank k ((D.endpointExtendedComplex k).homology i)=totalBetti k D.Variables (D.fullG k) i :=
  (regularExtendedPolynomialBetti (D.source.TangentAlgebra k) k D.a D.Variables
    (D.endpointElements k) (D.internalToG k) (D.internalVariableList k)
    (D.fullToG k) (D.fullVariableList k) (D.fullVariableList_actions k)
    (D.fullVariableList_mem k) (D.fullVariableList_nodup k) i).trans
      (totalBetti_iso k D.Variables (D.fullRegularIso k) i)

/-- Guards retain the actual H0 row and prevent Nat negative-index
truncation from introducing spurious higher-homology contributions. -/
noncomputable def endpointRemainder (i : ℕ) : ℕ :=
  (if 1 ≤ i then (D.actualP k+D.actualR k)*D.q.choose (i-1) else 0)+
    (if 2 ≤ i then D.actualR k*D.q.choose (i-2) else 0)

theorem endpoint_binomial_correction (i : ℕ) :
    binomialTransform D.q (fun j => if j=0 then 0 else
      Module.finrank k ((D.endpointComplex k).homology j)) i=D.endpointRemainder k i := by
  have he (j : ℕ) : (if j=0 then 0 else Module.finrank k ((D.endpointComplex k).homology j))=
      (if j=1 then D.actualP k+D.actualR k else 0)+(if j=2 then D.actualR k else 0) := by
    by_cases hj0 : j=0
    · simp [hj0]
    by_cases hj1 : j=1
    · subst j
      simpa using D.actualH1_dimension k
    by_cases hj2 : j=2
    · subst j
      simp [actualR]
    · simp only [hj0,hj1,hj2,ite_false,add_zero]
      exact D.endpointHomology_above k j (by omega)
  unfold binomialTransform
  simp_rw [he,mul_add,mul_ite,mul_zero]
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq',Finset.mem_range]
  unfold endpointRemainder
  congr 1 <;> split_ifs <;> first | omega | ac_rfl

/-- Actual double-Koszul comparison for the same G, same endpoints,
and same internal action. All Betti rows, arbitrary original field. -/
theorem actual_native_endpoint_bound (i : ℕ) : totalBetti k D.Variables (D.fullG k) i≤
    totalBetti k D.a (D.QActualModule k) i+D.endpointRemainder k i := by
  let : ∀ j,Module.Finite k ((regularPartialCoefficientComplex k (D.source.TangentAlgebra k)
      (D.endpointElements k)).homology j) := fun j => D.endpointHomologyFinite k j
  have h := regularCorrectedComparison k (D.source.TangentAlgebra k) D.a
    (D.endpointElements k) (D.internalToG k) (D.internalVariableList k)
    (D.endpointH0Internal_finite k) i
  rw [D.internalVariableList_length] at h
  change Module.finrank k ((D.endpointExtendedComplex k).homology i)≤
    Module.finrank k ((actionH0SingleCoefficientComplex k (D.source.TangentAlgebra k) D.a
      (D.endpointElements k) (D.internalToG k) (variableList k D.a)).homology i)+
      binomialTransform D.q (fun j => if j=0 then 0 else Module.finrank k ((D.endpointComplex k).homology j)) i at h
  rw [D.endpointH0Internal_betti,D.endpointExtended_betti,D.endpoint_binomial_correction] at h
  exact h
end NSP14.Endpoint.Data
