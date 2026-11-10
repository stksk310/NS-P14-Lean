module

public import NSP14.Homological.Betti
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.RingTheory.TensorProduct.MvPolynomial

@[expose] public section

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped TensorProduct

namespace NSP14.Homological

universe u
variable (k L : Type u) [Field k] [Field L] [Algebra k L]

/-- Extension of actual coefficient vector spaces and their actual maps. -/
noncomputable def fieldExtension : ModuleCat.{u} k ⥤ ModuleCat.{u} L where
  obj V := ModuleCat.of L (L ⊗[k] V)
  map f := ModuleCat.ofHom (f.hom.baseChange L)
  map_id V := by apply ModuleCat.hom_ext; simp
  map_comp f g := by apply ModuleCat.hom_ext; simp [LinearMap.baseChange_comp]

noncomputable instance fieldExtension_additive : (fieldExtension k L).Additive :=
  ⟨by intros; apply ModuleCat.hom_ext; change LinearMap.baseChange L (_ + _) = _ + _; exact LinearMap.baseChange_add _ _⟩

theorem fieldExtension_exact (S : ShortComplex (ModuleCat.{u} k)) (hS : S.Exact) :
    (S.map (fieldExtension k L)).Exact := by
  rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact] at hS ⊢
  exact Module.Flat.lTensor_exact L hS

noncomputable instance fieldExtension_preservesFiniteLimits : PreservesFiniteLimits (fieldExtension k L) := by
  have he : PreservesFiniteLimits (fieldExtension k L) ∧ PreservesFiniteColimits (fieldExtension k L) :=
    ((Functor.exact_tfae (fieldExtension k L)).out 2 4).mp (fieldExtension_exact k L)
  exact he.1

noncomputable instance fieldExtension_preservesFiniteColimits : PreservesFiniteColimits (fieldExtension k L) := by
  have he : PreservesFiniteLimits (fieldExtension k L) ∧ PreservesFiniteColimits (fieldExtension k L) :=
    ((Functor.exact_tfae (fieldExtension k L)).out 2 4).mp (fieldExtension_exact k L)
  exact he.2

/-- Flat base change of homology, without finite-dimensional chain groups. -/
noncomputable def fieldExtensionHomologyIso (K : ChainComplex (ModuleCat.{u} k) ℕ) (i : ℕ) :
    (((fieldExtension k L).mapHomologicalComplex (ComplexShape.down ℕ)).obj K).homology i ≅
      (fieldExtension k L).obj (K.homology i) :=
  (K.sc i).mapHomologyIso (fieldExtension k L)

theorem fieldExtension_finite (V : ModuleCat.{u} k) [Module.Finite k V] :
    Module.Finite L ((fieldExtension k L).obj V) := by
  change Module.Finite L (L ⊗[k] V)
  infer_instance

theorem fieldExtension_finrank (V : ModuleCat.{u} k) :
    Module.finrank L ((fieldExtension k L).obj V)=Module.finrank k V := by
  change Module.finrank L (L ⊗[k] V)=_
  exact Module.finrank_baseChange

/-- The polynomial algebra base-change map preserves the variable set. -/
noncomputable def polynomialFieldExtension (σ : Type u) :
    L ⊗[k] VariableRing k σ ≃ₐ[L] VariableRing L σ :=
  MvPolynomial.scalarRTensorAlgEquiv

/-- This equality concerns actual flat scalar extension of a complex. A later identification
with a changed-coefficient Koszul complex must be supplied separately. -/
theorem fieldExtension_homology_finrank (K : ChainComplex (ModuleCat.{u} k) ℕ) (i : ℕ)
    [Module.Finite k (K.homology i)] :
    Module.finrank L ((((fieldExtension k L).mapHomologicalComplex (ComplexShape.down ℕ)).obj K).homology i)=
      Module.finrank k (K.homology i) :=
  (fieldExtensionHomologyIso k L K i).toLinearEquiv.finrank_eq.trans (fieldExtension_finrank k L _)

end NSP14.Homological
