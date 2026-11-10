module

public import NSP14.Semigroup.TangentCoordinates
public import NSP14.Semigroup.TangentScalars
public import NSP14.Semigroup.TangentAction
public import NSP14.Semigroup.HeadCoordinates
public import Mathlib.RingTheory.Ideal.Quotient.Operations

@[expose] public section

namespace NSP14.NumericalSemigroup

variable (S : NSP14.NumericalSemigroup) (k : Type*) [CommRing k] [Nontrivial k]

noncomputable def xElement : S.TangentAlgebra k := S.initialMonomial k S.multiplicityExponent

/-- Actual ring multiplication by x, as a k-linear map. -/
noncomputable def xMultiply : S.TangentAlgebra k →ₗ[k] S.TangentAlgebra k :=
  (LinearMap.mul k (S.TangentAlgebra k)).flip (S.xElement k)

omit [Nontrivial k] in
theorem xMultiply_initial_live (x : S.carrier) (hx : S.LiveExponent x) :
    S.xMultiply k (S.initialMonomial k x) = S.initialMonomial k (S.shiftExponent x) := by
  change S.initialMonomial k x * S.initialMonomial k S.multiplicityExponent = _
  apply S.initialMonomial_mul_live
  simpa only [LiveExponent, multiplicityExponent, S.order_multiplicity] using hx

theorem xMultiply_initial_dead (x : S.carrier) (hx : ¬S.LiveExponent x) :
    S.xMultiply k (S.initialMonomial k x) = 0 := by
  change S.initialMonomial k x * S.initialMonomial k S.multiplicityExponent = 0
  apply (S.initialMonomial_mul_eq_zero_iff k _ _).2
  have ht := (S.not_live_iff_terminal x).1 hx
  simpa only [multiplicityExponent, S.order_multiplicity] using ht.2

/-- The numerical live shift is the coefficient expression of actual multiplication. -/
theorem xMultiply_coordinates (a : S.TangentAlgebra k) :
    S.tangentCoordinates k (S.xMultiply k a) = S.coordinateShift k (S.tangentCoordinates k a) := by
  have heq : (S.tangentCoordinates k).toLinearMap.comp (S.xMultiply k) =
      (S.coordinateShift k).comp (S.tangentCoordinates k).toLinearMap := by
    apply (S.tangentBasis k).ext
    intro x
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, S.tangentBasis_eq_initial]
    by_cases hx : S.LiveExponent x
    · rw [S.xMultiply_initial_live k x hx, S.tangentCoordinates_initial,
        S.tangentCoordinates_initial, S.coordinateShift_single_live k x 1 hx]
    · rw [S.xMultiply_initial_dead k x hx, map_zero, S.tangentCoordinates_initial,
        S.coordinateShift_single_dead k x 1 hx]
  exact LinearMap.congr_fun heq a

theorem mem_xKernel_coordinates (a : S.TangentAlgebra k) :
    a ∈ (S.xMultiply k).ker ↔ S.tangentCoordinates k a ∈ (S.coordinateShift k).ker := by
  change S.xMultiply k a = 0 ↔ S.coordinateShift k (S.tangentCoordinates k a) = 0
  rw [← S.xMultiply_coordinates]
  exact (map_eq_zero_iff (S.tangentCoordinates k) (S.tangentCoordinates k).injective).symm

noncomputable def xKernelCoordinateEquiv :
    (S.xMultiply k).ker ≃ₗ[k] (S.coordinateShift k).ker where
  toFun a := ⟨S.tangentCoordinates k a.val, (S.mem_xKernel_coordinates k a.val).1 a.property⟩
  invFun b := ⟨(S.tangentCoordinates k).symm b.val, by
    apply (S.mem_xKernel_coordinates k _).2
    simpa only [LinearEquiv.apply_symm_apply] using b.property⟩
  left_inv a := by apply Subtype.ext; exact (S.tangentCoordinates k).symm_apply_apply a.val
  right_inv b := by apply Subtype.ext; exact (S.tangentCoordinates k).apply_symm_apply b.val
  map_add' a b := by apply Subtype.ext; exact map_add _ _ _
  map_smul' c a := by apply Subtype.ext; exact map_smul _ _ _

/-- Full actual kernel coordinates, including arbitrary linear combinations. -/
noncomputable def xKernelEquiv : (S.xMultiply k).ker ≃ₗ[k] (S.TerminalExponent →₀ k) :=
  (S.xKernelCoordinateEquiv k).trans (S.coordinateKernelEquiv k)

noncomputable def xKernelBasis : Module.Basis S.TerminalExponent k (S.xMultiply k).ker :=
  Finsupp.basisSingleOne.map (S.xKernelEquiv k).symm

theorem xMultiply_range : (S.xMultiply k).range =
    ((S.coordinateShift k).range).comap (S.tangentCoordinates k).toLinearMap := by
  ext a
  constructor
  · rintro ⟨b, rfl⟩
    exact ⟨S.tangentCoordinates k b, (S.xMultiply_coordinates k b).symm⟩
  · rintro ⟨f, hf⟩
    refine ⟨(S.tangentCoordinates k).symm f, ?_⟩
    apply (S.tangentCoordinates k).injective
    rw [S.xMultiply_coordinates, LinearEquiv.apply_symm_apply]
    exact hf

noncomputable def actualHeadProjection : S.TangentAlgebra k →ₗ[k] (S.HeadExponent →₀ k) :=
  (S.headProjection k).comp (S.tangentCoordinates k).toLinearMap

omit [Nontrivial k] in
theorem actualHeadProjection_surjective : Function.Surjective (S.actualHeadProjection k) :=
  (S.headProjection_surjective k).comp (S.tangentCoordinates k).surjective

theorem actualHeadProjection_ker : (S.actualHeadProjection k).ker = (S.xMultiply k).range := by
  rw [actualHeadProjection, LinearMap.ker_comp, S.headProjection_ker, S.xMultiply_range]

noncomputable def headCokernelEquiv :
    (S.TangentAlgebra k ⧸ (S.xMultiply k).range) ≃ₗ[k] (S.HeadExponent →₀ k) :=
  (Submodule.quotEquivOfEq _ _ (S.actualHeadProjection_ker k).symm).trans
    ((S.actualHeadProjection k).quotKerEquivOfSurjective (S.actualHeadProjection_surjective k))

/-- The actual principal ideal xG. -/
noncomputable def xIdeal : Ideal (S.TangentAlgebra k) := Ideal.span {S.xElement k}

omit [Nontrivial k] in
theorem xIdeal_eq_range : (S.xIdeal k).restrictScalars k = (S.xMultiply k).range := by
  ext a
  change a ∈ Ideal.span {S.xElement k} ↔ ∃ b, S.xMultiply k b = a
  rw [Ideal.mem_span_singleton]
  rw [dvd_def]
  constructor
  · rintro ⟨b, hb⟩
    refine ⟨b, ?_⟩
    change b * S.xElement k = a
    rw [mul_comm]
    exact hb.symm
  · rintro ⟨b, hb⟩
    refine ⟨b, ?_⟩
    change b * S.xElement k = a at hb
    simpa only [mul_comm] using hb.symm

abbrev HeadAlgebra := S.TangentAlgebra k ⧸ S.xIdeal k

/-- A=G/xG is an actual ring quotient with the numerical x-heads as a k-basis. -/
noncomputable def headQuotientEquiv : S.HeadAlgebra k ≃ₗ[k] (S.HeadExponent →₀ k) :=
  (Submodule.quotEquivOfEq _ _ (S.xIdeal_eq_range k)).trans (S.headCokernelEquiv k)

noncomputable def headBasis : Module.Basis S.HeadExponent k (S.HeadAlgebra k) :=
  Finsupp.basisSingleOne.map (S.headQuotientEquiv k).symm

end NSP14.NumericalSemigroup
