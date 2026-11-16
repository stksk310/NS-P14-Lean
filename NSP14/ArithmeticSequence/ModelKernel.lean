module
public import NSP14.ArithmeticSequence.ModelQuotient
@[expose] public section
open scoped Classical
namespace NSP14.ArithmeticSequence.Data
variable (D : NSP14.ArithmeticSequence.Data) (hv : 2 ≤ D.v) (k : Type) [Field k]

theorem headIndexMonomial_coordinates (i : ℕ) (j : Fin D.m) :
    D.source.headQuotientEquiv k (D.headIndexMonomial k i) (D.headIndexEquiv j)=
      if i=j.val then 1 else 0 := by
  change D.source.headQuotientEquiv k (D.source.headMonomial k _) (D.headIndexEquiv j)=_
  rw [D.source.headMonomial_coordinates]
  by_cases he : i=j.val
  · subst i
    simp only [ite_true]
    exact Finsupp.single_eq_same
  · rw [ite_eq_right he]
    apply Finsupp.single_eq_of_ne
    intro h
    apply he
    exact (D.aperyValue_strictMono.injective (congrArg Subtype.val h)).symm

theorem modelToHead_coordinates (a : (D.ordinaryModel hv).source.TangentAlgebra k) (j : Fin D.m) :
    D.source.headQuotientEquiv k (D.modelToHead hv k a) (D.headIndexEquiv j)=
      (D.modelBasis hv k).repr a j.val := by
  let L : (D.ordinaryModel hv).source.TangentAlgebra k →ₗ[k] k :=
    (Finsupp.lapply (D.headIndexEquiv j)).comp
      ((D.source.headQuotientEquiv k).toLinearMap.comp (D.modelToHead hv k).toLinearMap)
  let R : (D.ordinaryModel hv).source.TangentAlgebra k →ₗ[k] k :=
    (Finsupp.lapply j.val).comp (D.modelBasis hv k).repr.toLinearMap
  have he : L=R := by
    apply (D.modelBasis hv k).ext
    intro i
    change D.source.headQuotientEquiv k (D.modelToHeadLinear hv k (D.modelBasis hv k i))
      (D.headIndexEquiv j)=(D.modelBasis hv k).repr (D.modelBasis hv k i) j.val
    rw [Module.Basis.repr_self,D.modelBasis_eq_monomial,D.modelToHeadLinear_monomial,D.headIndexMonomial_coordinates]
    simp only [Finsupp.single_apply]
  exact LinearMap.congr_fun he a

/-- The actual ideal of the actual surjection, rather than a support
space used in place of its kernel. -/
noncomputable def modelKernel : Ideal ((D.ordinaryModel hv).source.TangentAlgebra k) :=
  RingHom.ker (D.modelToHead hv k)

theorem mem_modelKernel (a : (D.ordinaryModel hv).source.TangentAlgebra k) :
    a ∈ D.modelKernel hv k ↔ ∀ i : Fin D.m,(D.modelBasis hv k).repr a i.val=0 := by
  change D.modelToHead hv k a=0 ↔ _
  constructor
  · intro h i
    have he := congrArg (fun z => D.source.headQuotientEquiv k z (D.headIndexEquiv i)) h
    simpa only [D.modelToHead_coordinates,map_zero,Finsupp.zero_apply] using he
  · intro h
    apply (D.source.headQuotientEquiv k).injective
    ext y
    obtain ⟨i,rfl⟩ := D.headIndexEquiv.surjective y
    rw [D.modelToHead_coordinates,map_zero,Finsupp.zero_apply]
    exact h i

noncomputable def modelKernelCoordinates :
    D.modelKernel hv k ≃ₗ[k] ({i : ℕ // D.m ≤ i} →₀ k) where
  toFun a := ((D.modelBasis hv k).repr a.val).subtypeDomain (fun i => D.m ≤ i)
  invFun f := ⟨(D.modelBasis hv k).repr.symm f.extendDomain,by
    rw [D.mem_modelKernel]
    intro i
    rw [LinearEquiv.apply_symm_apply]
    rw [Finsupp.extendDomain_apply]
    simp [not_le_of_gt i.isLt]⟩
  left_inv a := by
    apply Subtype.ext
    apply (D.modelBasis hv k).repr.injective
    rw [LinearEquiv.apply_symm_apply]
    ext i
    rw [Finsupp.extendDomain_apply]
    by_cases hi : D.m ≤ i
    · rw [dite_eq_left hi]
      rfl
    · rw [dite_eq_right hi]
      exact ((D.mem_modelKernel hv k a.val).mp a.property ⟨i,by omega⟩).symm
  right_inv f := by
    change Finsupp.subtypeDomain (fun i => D.m ≤ i)
      ((D.modelBasis hv k).repr ((D.modelBasis hv k).repr.symm f.extendDomain))=f
    rw [LinearEquiv.apply_symm_apply,Finsupp.subtypeDomain_extendDomain]
  map_add' a b := by
    change ((D.modelBasis hv k).repr (a.val+b.val)).subtypeDomain _=_
    rw [map_add,Finsupp.subtypeDomain_add]
  map_smul' c a := by
    change ((D.modelBasis hv k).repr (c • a.val)).subtypeDomain _=_
    rw [map_smul]
    ext i
    rfl

noncomputable def modelKernelBasis : Module.Basis {i : ℕ // D.m ≤ i} k (D.modelKernel hv k) :=
  Finsupp.basisSingleOne.map (D.modelKernelCoordinates hv k).symm

noncomputable def modelKernelMonomial (i : {i : ℕ // D.m ≤ i}) : D.modelKernel hv k :=
  ⟨D.modelMonomial hv k i.val,by
    change D.modelToHeadLinear hv k (D.modelMonomial hv k i.val)=0
    rw [D.modelToHeadLinear_monomial,D.headIndexMonomial_zero k i.property]⟩

theorem modelKernelBasis_monomial (i : {i : ℕ // D.m ≤ i}) :
    D.modelKernelBasis hv k i=D.modelKernelMonomial hv k i := by
  apply (D.modelKernelCoordinates hv k).injective
  change (D.modelKernelCoordinates hv k)
      ((D.modelKernelCoordinates hv k).symm (Finsupp.single i 1))=_
  rw [LinearEquiv.apply_symm_apply]
  ext j
  change Finsupp.single i (1:k) j=
    (D.modelBasis hv k).repr (D.modelMonomial hv k i.val) j.val
  rw [← D.modelBasis_eq_monomial hv k,Module.Basis.repr_self]
  by_cases he : i=j
  · subst j;simp
  · have hn : i.val≠j.val := fun h => he (Subtype.ext h)
    simp [he,hn]
end NSP14.ArithmeticSequence.Data
