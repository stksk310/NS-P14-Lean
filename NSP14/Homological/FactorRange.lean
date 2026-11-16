module
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
@[expose] public section
namespace NSP14.Homological
variable (k : Type*) [Field k] {X Y C U : Type*}
  [AddCommGroup X] [Module k X] [AddCommGroup Y] [Module k Y]
  [AddCommGroup C] [Module k C] [AddCommGroup U] [Module k U]

/-- A surjective projection and an injective inclusion preserve the
rank of the intervening actual boundary. No source finiteness is assumed. -/
theorem factorization_range_finrank (d : X →ₗ[k] Y) (f : C →ₗ[k] U)
    (p : X →ₗ[k] C) (q : U →ₗ[k] Y)
    (hp : Function.Surjective p) (hq : Function.Injective q)
    (hd : d=q.comp (f.comp p)) : Module.finrank k d.range=Module.finrank k f.range := by
  have he : d.range=f.range.map q := by
    rw [hd,← LinearMap.comp_assoc,
      LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top.mpr hp),LinearMap.range_comp]
  rw [he]
  exact (Submodule.equivMapOfInjective q hq f.range).finrank_eq.symm
end NSP14.Homological
