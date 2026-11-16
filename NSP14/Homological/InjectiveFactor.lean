module
public import Mathlib.LinearAlgebra.Isomorphisms
@[expose] public section
namespace NSP14.Homological
variable (R : Type*) [CommRing R] {X Y Z : Type*}
  [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R Y] [AddCommGroup Z] [Module R Z]
  (f : X →ₗ[R] Y) (hf : Function.Injective f) (g : Z →ₗ[R] Y)
  (hg : ∀ z,g z∈f.range)

/-- Division through an actual injective module map on its actual image. -/
noncomputable def injectiveFactor : Z →ₗ[R] X :=
  (LinearEquiv.ofInjective f hf).symm.toLinearMap.comp (g.codRestrict f.range hg)

theorem injectiveFactor_comp (z : Z) : f (injectiveFactor R f hf g hg z)=g z :=
  congrArg Subtype.val ((LinearEquiv.ofInjective f hf).apply_symm_apply ⟨g z,hg z⟩)
end NSP14.Homological
