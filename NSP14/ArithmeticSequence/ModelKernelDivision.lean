module
public import NSP14.ArithmeticSequence.ModelExactSequence
public import NSP14.Homological.InjectiveFactor
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory NSP14.Homological
namespace NSP14.ArithmeticSequence.Data
variable (D : NSP14.ArithmeticSequence.Data) (hv : 2 ≤ D.v) (k : Type) [Field k]

noncomputable def modelNativeX : D.modelRegularNative hv k ⟶ D.modelRegularNative hv k :=
  ((D.ordinaryModel hv).source.xElement k) • 𝟙 (D.modelRegularNative hv k)

theorem modelNativeX_injective : Function.Injective (D.modelNativeX hv k).hom := by
  intro a b h
  apply (D.ordinaryModel hv).xMultiply_injective k
  change a*(D.ordinaryModel hv).source.xElement k=b*(D.ordinaryModel hv).source.xElement k
  change (D.ordinaryModel hv).source.xElement k*a=(D.ordinaryModel hv).source.xElement k*b at h
  simpa only [mul_comm] using h

/-- Every actual kernel element is divisible by x in B. The strict
minimality condition m>v supplies the entire assertion. -/
theorem modelKernelIn_xRange (a : D.modelKernel hv k) :
    (D.modelKernelNativeInclusion hv k).hom a∈(D.modelNativeX hv k).hom.range := by
  let T : Submodule k (D.modelKernel hv k) :=
    ((D.modelNativeX hv k).hom.range.restrictScalars k).comap
      ((D.modelKernelNativeInclusion hv k).hom.restrictScalars k)
  have hT : T=⊤ := by
    apply top_unique
    rw [← (D.modelKernelNatBasis hv k).span_eq]
    apply Submodule.span_le.mpr
    rintro _ ⟨n,rfl⟩
    change (D.modelKernelNatBasis hv k n).val∈(D.modelNativeX hv k).hom.range
    refine ⟨D.modelMonomial hv k (D.m+n-D.v),?_⟩
    rw [D.modelKernelNatBasis_monomial]
    change (D.ordinaryModel hv).source.xElement k*D.modelMonomial hv k (D.m+n-D.v)=
      D.modelMonomial hv k (D.m+n)
    rw [D.modelMultiplicityMonomial,mul_comm,D.modelMonomial_mul,D.blockCount_add_v,D.blockCount_v,
      ite_eq_left rfl,Nat.sub_add_cancel (show D.v ≤ D.m+n by have := D.v_lt;omega)]
  have ha : a∈T := by rw [hT];trivial
  exact ha

noncomputable def modelKernelNativeDivision : D.modelKernelNative hv k ⟶ D.modelRegularNative hv k :=
  ModuleCat.ofHom (injectiveFactor ((D.ordinaryModel hv).source.TangentAlgebra k)
    (D.modelNativeX hv k).hom (D.modelNativeX_injective hv k)
    (D.modelKernelNativeInclusion hv k).hom (D.modelKernelIn_xRange hv k))

theorem modelKernelNativeDivision_comp :
    D.modelKernelNativeDivision hv k ≫ D.modelNativeX hv k=D.modelKernelNativeInclusion hv k := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  exact injectiveFactor_comp ((D.ordinaryModel hv).source.TangentAlgebra k)
    (D.modelNativeX hv k).hom (D.modelNativeX_injective hv k)
    (D.modelKernelNativeInclusion hv k).hom (D.modelKernelIn_xRange hv k) a

noncomputable def modelKernelFullDivision : D.modelKernelFull hv k ⟶ D.modelRegularFull hv k :=
  (ModuleCat.restrictScalars (D.modelFullPolynomial hv k).toRingHom).map (D.modelKernelNativeDivision hv k)

/-- Inclusion into B is a genuine last-variable multiple of a genuine
polynomial-linear map; this will force every induced Tor map to zero. -/
theorem modelKernelFullInclusion_factor :
    D.modelKernelFullInclusion hv k=D.modelKernelFullDivision hv k ≫
      ((MvPolynomial.X (⟨D.v-1,by omega⟩ : Fin D.v) : VariableRing k (Fin D.v)) • 𝟙 (D.modelRegularFull hv k)) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  have h := congrArg (fun f => f.hom a) (D.modelKernelNativeDivision_comp hv k)
  change (D.ordinaryModel hv).source.xElement k*((D.modelKernelNativeDivision hv k).hom a)=a.val at h
  change a.val=D.modelFullPolynomial hv k (MvPolynomial.X ⟨D.v-1,by omega⟩)*
    ((D.modelKernelNativeDivision hv k).hom a)
  rw [D.modelFullPolynomial_X,Nat.sub_add_cancel (show 1 ≤ D.v by omega),← D.modelMultiplicityMonomial hv k]
  exact h.symm
end NSP14.ArithmeticSequence.Data
