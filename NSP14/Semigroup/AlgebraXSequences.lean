module
public import NSP14.Semigroup.CutAction
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory
namespace NSP14.NumericalSemigroup
variable (S : NumericalSemigroup) (k : Type) [Field k]

noncomputable def algebraG : ModuleCat (S.TangentAlgebra k) := ModuleCat.of _ (S.TangentAlgebra k)
noncomputable def algebraT : ModuleCat (S.TangentAlgebra k) := ModuleCat.of _ (S.terminalIdeal k)
noncomputable def algebraI : ModuleCat (S.TangentAlgebra k) := ModuleCat.of _ (S.xIdeal k)
noncomputable def algebraA : ModuleCat (S.TangentAlgebra k) := ModuleCat.of _ (S.HeadAlgebra k)

noncomputable def algebraTerminalInclusion : S.algebraT k ⟶ S.algebraG k :=
  ModuleCat.ofHom (X:=S.algebraT k) (Y:=S.algebraG k)
    { toFun a := a.val
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }

noncomputable def algebraXProjection : S.algebraG k ⟶ S.algebraI k :=
  ModuleCat.ofHom (X:=S.algebraG k) (Y:=S.algebraI k)
    { toFun a := ⟨(show S.TangentAlgebra k from a)*S.xElement k,
        Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_singleton _))⟩
      map_add' _a _b := Subtype.ext (add_mul _ _ _)
      map_smul' _p _a := Subtype.ext (mul_assoc _ _ _) }

noncomputable def algebraImageInclusion : S.algebraI k ⟶ S.algebraG k :=
  ModuleCat.ofHom (X:=S.algebraI k) (Y:=S.algebraG k)
    { toFun a := a.val
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }

noncomputable def algebraHeadProjection : S.algebraG k ⟶ S.algebraA k :=
  ModuleCat.ofHom (X:=S.algebraG k) (Y:=S.algebraA k)
    { toFun a := Ideal.Quotient.mk (S.xIdeal k) a
      map_add' a b := map_add _ a b
      map_smul' p a := map_mul (Ideal.Quotient.mk _) p a }

theorem algebraTerminal_comp : S.algebraTerminalInclusion k ≫ S.algebraXProjection k=0 := by
  ext a
  apply Subtype.ext
  exact a.property

theorem algebraImage_comp : S.algebraImageInclusion k ≫ S.algebraHeadProjection k=0 := by
  ext a
  exact Ideal.Quotient.eq_zero_iff_mem.mpr a.property

noncomputable def algebraKernelSequence : ShortComplex (ModuleCat (S.TangentAlgebra k)) :=
  ShortComplex.mk _ _ (S.algebraTerminal_comp k)

noncomputable def algebraHeadSequence : ShortComplex (ModuleCat (S.TangentAlgebra k)) :=
  ShortComplex.mk _ _ (S.algebraImage_comp k)

theorem algebraKernelSequence_shortExact : (S.algebraKernelSequence k).ShortExact := by
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · rw [ShortComplex.moduleCat_exact_iff]
    intro a ha
    exact ⟨⟨a,congrArg Subtype.val ha⟩,rfl⟩
  · rw [ModuleCat.mono_iff_injective]
    exact Subtype.val_injective
  · rw [ModuleCat.epi_iff_surjective]
    intro a
    have hm : a.val ∈ (S.xMultiply k).range := by
      rw [← S.xIdeal_eq_range k]
      exact a.property
    obtain ⟨b,hb⟩ := hm
    exact ⟨b,Subtype.ext hb⟩

theorem algebraHeadSequence_shortExact : (S.algebraHeadSequence k).ShortExact := by
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · rw [ShortComplex.moduleCat_exact_iff]
    intro a ha
    exact ⟨⟨a,Ideal.Quotient.eq_zero_iff_mem.mp ha⟩,rfl⟩
  · rw [ModuleCat.mono_iff_injective]
    exact Subtype.val_injective
  · rw [ModuleCat.epi_iff_surjective]
    change Function.Surjective (Ideal.Quotient.mk (S.xIdeal k))
    exact Ideal.Quotient.mk_surjective
end NSP14.NumericalSemigroup
