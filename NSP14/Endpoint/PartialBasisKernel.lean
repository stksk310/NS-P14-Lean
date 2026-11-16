module
public import Mathlib.LinearAlgebra.Finsupp.Supported
public import Mathlib.LinearAlgebra.Basis.Basic
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open scoped Classical
namespace NSP14.Endpoint
variable (k I V : Type) [Field k] [AddCommGroup V] [Module k V]
  (b : Module.Basis I k V) (L : V →ₗ[k] V) (P : I → Prop)
  (f : {i : I // P i} → I) (hinj : Function.Injective f)

noncomputable def partialCoordinateShift : (I →₀ k) →ₗ[k] (I →₀ k) :=
  (Finsupp.lmapDomain k k f).comp (Finsupp.lsubtypeDomain {i : I | P i})

include hinj in
theorem partialCoordinateShift_zero (a : I →₀ k) : partialCoordinateShift k I P f a=0 ↔ ∀ i,P i → a i=0 := by
  change Finsupp.mapDomain f (a.subtypeDomain P)=0 ↔ _
  rw [←Finsupp.mapDomain_zero (f:=f),(Finsupp.mapDomain_injective hinj).eq_iff]
  constructor
  · intro h i hi
    exact congrArg (fun g => g ⟨i,hi⟩) h
  · intro h
    ext i
    exact h i.val i.property

variable (hL : ∀ i,L (b i)=if h : P i then b (f ⟨i,h⟩) else 0)
include hL in
theorem partial_basis_coordinates (a : V) : b.repr (L a)=partialCoordinateShift k I P f (b.repr a) := by
  have he : b.repr.toLinearMap.comp L=(partialCoordinateShift k I P f).comp b.repr.toLinearMap := by
    apply b.ext
    intro i
    simp only [LinearMap.comp_apply,LinearEquiv.coe_coe,hL,b.repr_self]
    split_ifs with hi
    · rw [b.repr_self]
      change Finsupp.single (f ⟨i,hi⟩) 1=Finsupp.mapDomain f ((Finsupp.single i 1).subtypeDomain P)
      have hz : (Finsupp.single i (1:k)).subtypeDomain P=Finsupp.single ⟨i,hi⟩ 1 := by
        ext j
        change Finsupp.single i (1:k) j.val=Finsupp.single ⟨i,hi⟩ (1:k) j
        by_cases he : j=⟨i,hi⟩
        · subst j
          simp only [Finsupp.single_eq_same]
        · have hj : j.val≠i := fun hh => he (Subtype.ext hh)
          rw [Finsupp.single_eq_of_ne hj,Finsupp.single_eq_of_ne he]
      rw [hz,Finsupp.mapDomain_single]
    · rw [map_zero]
      change 0=Finsupp.mapDomain f ((Finsupp.single i 1).subtypeDomain P)
      have hz : (Finsupp.single i (1:k)).subtypeDomain P=0 := by
        ext j
        change Finsupp.single i (1:k) j.val=0
        exact Finsupp.single_eq_of_ne (fun he => hi (he ▸ j.property))
      rw [hz,Finsupp.mapDomain_zero]
  exact LinearMap.congr_fun he a

include hL hinj in
theorem partial_basis_kernel (a : V) : L a=0 ↔ ∀ i,P i → b.repr a i=0 := by
  rw [←(map_eq_zero_iff b.repr b.repr.injective),partial_basis_coordinates k I V b L P f hL]
  exact partialCoordinateShift_zero k I P f hinj _
end NSP14.Endpoint
