module
public import NSP14.ArithmeticSequence.ModelMultiplication
@[expose] public section
open scoped Classical
namespace NSP14.ArithmeticSequence.Data
variable (D : NSP14.ArithmeticSequence.Data) (hv : 2 ≤ D.v) (k : Type) [Field k]

noncomputable def modelBasis : Module.Basis ℕ k ((D.ordinaryModel hv).source.TangentAlgebra k) :=
  ((D.ordinaryModel hv).source.tangentBasis k).reindex (D.modelExponentEquiv hv).symm

theorem modelBasis_eq_monomial (i : ℕ) : D.modelBasis hv k i=D.modelMonomial hv k i := by
  rw [modelBasis,Module.Basis.reindex_apply]
  exact (D.ordinaryModel hv).source.tangentBasis_eq_initial k (D.modelExponentEquiv hv i)

noncomputable def modelToHeadLinear :
    (D.ordinaryModel hv).source.TangentAlgebra k →ₗ[k] D.source.HeadAlgebra k :=
  (D.modelBasis hv k).constr k (D.headIndexMonomial k)

theorem modelToHeadLinear_monomial (i : ℕ) :
    D.modelToHeadLinear hv k (D.modelMonomial hv k i)=D.headIndexMonomial k i := by
  rw [← D.modelBasis_eq_monomial hv k]
  exact Module.Basis.constr_basis _ _ _ _

theorem modelToHeadLinear_one : D.modelToHeadLinear hv k 1=1 := by
  have hB : D.modelMonomial hv k 0=1 := by
    change (D.ordinaryModel hv).source.initialMonomial k _=1
    have he : (⟨D.modelExponent 0,D.modelExponent_mem hv 0⟩ : (D.ordinaryModel hv).source.carrier)=0 :=
      Subtype.ext (by simp [modelExponent,D.blockCount_zero])
    rw [he,(D.ordinaryModel hv).source.initialMonomial_zero]
  rw [← hB,D.modelToHeadLinear_monomial]
  change D.source.headMonomial k _=1
  have he : (⟨D.aperyValue 0,D.aperyValue_mem_source 0⟩ : D.source.carrier)=0 :=
    Subtype.ext (by simp [aperyValue,D.blockCount_zero])
  rw [he]
  change Ideal.Quotient.mk _ (D.source.initialMonomial k 0)=1
  rw [D.source.initialMonomial_zero,map_one]

theorem modelToHeadLinear_mul (a b : (D.ordinaryModel hv).source.TangentAlgebra k) :
    D.modelToHeadLinear hv k (a*b)=D.modelToHeadLinear hv k a*D.modelToHeadLinear hv k b := by
  let f := D.modelToHeadLinear hv k
  let L := (LinearMap.mul k ((D.ordinaryModel hv).source.TangentAlgebra k)).compr₂ f
  let R := (LinearMap.mul k (D.source.HeadAlgebra k)).compl₁₂ f f
  have he : L=R := by
    apply (D.modelBasis hv k).ext
    intro i
    apply (D.modelBasis hv k).ext
    intro j
    change f (D.modelBasis hv k i*D.modelBasis hv k j)=f (D.modelBasis hv k i)*f (D.modelBasis hv k j)
    rw [D.modelBasis_eq_monomial,D.modelBasis_eq_monomial,D.modelMonomial_mul,
      D.modelToHeadLinear_monomial,D.modelToHeadLinear_monomial,D.headIndexMonomial_mul]
    split_ifs
    · exact D.modelToHeadLinear_monomial hv k (i+j)
    · exact map_zero f
  exact LinearMap.congr_fun (LinearMap.congr_fun he a) b

/-- A genuine surjective algebra map from the ordinary auxiliary cone
onto the actual finite AP head algebra. -/
noncomputable def modelToHead :
    (D.ordinaryModel hv).source.TangentAlgebra k →ₐ[k] D.source.HeadAlgebra k :=
  AlgHom.ofLinearMap (D.modelToHeadLinear hv k) (D.modelToHeadLinear_one hv k) (D.modelToHeadLinear_mul hv k)

theorem modelToHead_surjective : Function.Surjective (D.modelToHead hv k) := by
  intro a
  let b := D.source.headBasis k
  have h : LinearMap.range (D.modelToHead hv k).toLinearMap=⊤ := by
    apply top_unique
    rw [← b.span_eq]
    apply Submodule.span_le.mpr
    rintro _ ⟨i,rfl⟩
    let n := (D.headIndexEquiv.symm i).val
    refine ⟨D.modelMonomial hv k n,?_⟩
    change D.modelToHeadLinear hv k (D.modelMonomial hv k n)=b i
    rw [D.modelToHeadLinear_monomial]
    have he := D.headIndexMonomial_basis k (D.headIndexEquiv.symm i)
    simpa only [Equiv.apply_symm_apply] using he
  exact LinearMap.range_eq_top.mp h a
end NSP14.ArithmeticSequence.Data
