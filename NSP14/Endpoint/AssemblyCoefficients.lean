module
public import NSP14.Endpoint.FiberModule
public import NSP14.Endpoint.KernelIdeals
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open scoped Classical DirectSum
namespace NSP14.Endpoint.Data
variable (D : NSP14.Endpoint.Data) (k : Type) [Field k]

theorem fiberPolynomialPoint_injective : Function.Injective
    (fun b : D.FiberBasisIndex => D.fiberPolynomialPoint b.1 b.2) :=
  (D.fiberPolynomialIndexEquiv).injective

/-- Coefficient extraction in the actual E-module assembly. Distinct
residues and distinct monomials cannot cancel after assembly. -/
theorem coreFiberLinearAssembly_coeff (f : ⨁ r : Fin D.u,D.coreFiberIdeal k r)
    (b : D.FiberBasisIndex) :
    (D.coreFiberLinearAssembly k f).coeff (D.fiberPolynomialPoint b.1 b.2)=
      (f b.1).val.coeff b.2.val := by
  let l1 : (⨁ r : Fin D.u,D.coreFiberIdeal k r) →ₗ[k] k :=
    (Finsupp.lapply (D.fiberPolynomialPoint b.1 b.2)).comp
      ((AddMonoidAlgebra.coeffLinearEquiv k).toLinearMap.comp (D.coreFiberLinearAssembly k).toLinearMap)
  let l2 : (⨁ r : Fin D.u,D.coreFiberIdeal k r) →ₗ[k] k :=
    {toFun := fun f => (f b.1).val.coeff b.2.val
     map_add' := by intro x y;change (x b.1+y b.1).val.coeff b.2.val=_;simp
     map_smul' := by intro c x;change (c • x b.1).val.coeff b.2.val=_;simp}
  have he : l1=l2 := by
    apply (D.coreSumBasis k).ext
    rintro ⟨r,a⟩
    change (D.coreFiberLinearAssembly k (D.coreSumBasis k ⟨r,a⟩)).coeff _=_
    rw [D.coreFiberLinearAssembly_basis]
    change (AddMonoidAlgebra.single (D.fiberPolynomialPoint r a) (1:k)).coeff _=_
    rw [AddMonoidAlgebra.coeff_single,Finsupp.single_apply]
    change (if D.fiberPolynomialPoint r a=D.fiberPolynomialPoint b.1 b.2 then (1:k) else 0)=
      ((D.coreSumBasis k ⟨r,a⟩) b.1).val.coeff b.2.val
    rw [D.coreSumBasis_apply]
    by_cases hr : r=b.1
    · subst r
      simp only [DFinsupp.single_eq_same,D.coreFiberBasis_val,MvPolynomial.coeff_monomial]
      congr 1
      apply propext
      constructor
      · intro h
        have hh := D.fiberPolynomialIndexEquiv.injective (show D.fiberPolynomialIndexEquiv ⟨b.1,a⟩=D.fiberPolynomialIndexEquiv b from h)
        exact congrArg (fun a : {a : Fin 2 →₀ ℕ // (a 0,a 1)∈D.coreFiber b.1} => a.val)
          (eq_of_heq (Sigma.mk.inj_iff.mp hh).2)
      · intro h
        have ha : a=b.2 := Subtype.ext h
        rw [ha]
    · have hne : D.fiberPolynomialPoint r a≠D.fiberPolynomialPoint b.1 b.2 := by
        intro h
        exact hr (congrArg Sigma.fst (D.fiberPolynomialIndexEquiv.injective
          (show D.fiberPolynomialIndexEquiv ⟨r,a⟩=D.fiberPolynomialIndexEquiv b from h)))
      simp only [hne,ite_false,DFinsupp.single_eq_of_ne (Ne.symm hr),ZeroMemClass.coe_zero,AddMonoidAlgebra.coeff_zero,Finsupp.zero_apply]
  exact LinearMap.congr_fun he f
end NSP14.Endpoint.Data
