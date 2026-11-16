module
public import Mathlib.LinearAlgebra.Finsupp.VectorSpace
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.LinearAlgebra.Isomorphisms
@[expose] public section
open scoped BigOperators Classical
namespace NSP14.Homological
variable (k : Type*) [Field k] {M : Type*} [AddCommGroup M] [Module k M]
  (b : Module.Basis ℕ k M) (v : ℕ) (X : M →ₗ[k] M)

noncomputable def basisWindowProjection : M →ₗ[k] (Fin v → k) :=
  LinearMap.pi (fun i => (Finsupp.lapply i.val).comp b.repr.toLinearMap)

include b in
theorem basisWindowProjection_surjective : Function.Surjective (basisWindowProjection k b v) := by
  intro f
  refine ⟨∑ i : Fin v,f i • b i.val,?_⟩
  ext j
  let L : M →ₗ[k] k := (Finsupp.lapply j.val).comp b.repr.toLinearMap
  change L (∑ i : Fin v,f i • b i.val)=f j
  simp only [map_sum,map_smul]
  change (∑ i : Fin v,f i*b.repr (b i.val) j.val)=f j
  simp only [Module.Basis.repr_self,Finsupp.single_apply]
  rw [Fintype.sum_eq_single j]
  · simp
  · intro i hi
    have hn : i.val≠j.val := fun h => hi (Fin.ext h)
    simp [hn]

include b in
theorem basisShift_coordinates (hX : ∀ i,X (b i)=b (i+v)) (a : M) :
    b.repr (X a)=Finsupp.mapDomain (fun i => i+v) (b.repr a) := by
  let L := b.repr.toLinearMap.comp X
  let R := (Finsupp.lmapDomain k k (fun i : ℕ => i+v)).comp b.repr.toLinearMap
  have he : L=R := by
    apply b.ext
    intro i
    change b.repr (X (b i))=Finsupp.mapDomain (fun i => i+v) (b.repr (b i))
    rw [hX,Module.Basis.repr_self,Module.Basis.repr_self,Finsupp.mapDomain_single]
  exact LinearMap.congr_fun he a

include b in
theorem basisWindowProjection_ker (hX : ∀ i,X (b i)=b (i+v)) :
    (basisWindowProjection k b v).ker=X.range := by
  apply le_antisymm
  · intro a ha
    have hz (i : Fin v) : b.repr a i.val=0 := congrFun ha i
    let f := b.repr a
    have hinj : Function.Injective (fun i : ℕ => i+v) := fun _ _ h => Nat.add_right_cancel h
    let g := Finsupp.comapDomain (fun i : ℕ => i+v) f hinj.injOn
    refine ⟨b.repr.symm g,?_⟩
    apply b.repr.injective
    rw [basisShift_coordinates k b v X hX,LinearEquiv.apply_symm_apply]
    apply Finsupp.mapDomain_comapDomain (fun i : ℕ => i+v) hinj f
    intro i hi
    have hvi : v ≤ i := by
      by_contra hn
      exact Finsupp.mem_support_iff.mp hi (hz ⟨i,by omega⟩)
    exact ⟨i-v,Nat.sub_add_cancel hvi⟩
  · rintro _ ⟨a,rfl⟩
    change basisWindowProjection k b v (X a)=0
    ext i
    change b.repr (X a) i.val=0
    rw [basisShift_coordinates k b v X hX]
    apply Finsupp.mapDomain_of_notMem_range
    rintro ⟨n,he⟩
    have hi := i.isLt
    change n+v=i.val at he
    omega

noncomputable def basisShiftQuotientEquiv (hX : ∀ i,X (b i)=b (i+v)) :
    (M ⧸ X.range) ≃ₗ[k] (Fin v → k) :=
  (Submodule.quotEquivOfEq _ _ (basisWindowProjection_ker k b v X hX).symm).trans
    ((basisWindowProjection k b v).quotKerEquivOfSurjective (basisWindowProjection_surjective k b v))

theorem basisShiftQuotientEquiv_mk (hX : ∀ i,X (b i)=b (i+v)) (a : M) :
    basisShiftQuotientEquiv k b v X hX (Submodule.Quotient.mk a)=basisWindowProjection k b v a := rfl
end NSP14.Homological
