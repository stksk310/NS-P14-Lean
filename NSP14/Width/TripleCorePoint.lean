module
public import NSP14.Width.AntipodalCore
public import NSP14.Endpoint.InternalMonoid
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open scoped Classical BigOperators
namespace NSP14.Endpoint.Data
variable (D : NSP14.Endpoint.Data)

def triplePoint (v : Fin 3 ≃ D.a) (x y z : ℕ) : D.corePoints :=
  x • D.coreGeneratorPoint (D.internalVariable (v 0))+
  y • D.coreGeneratorPoint (D.internalVariable (v 1))+
  z • D.coreGeneratorPoint (D.internalVariable (v 2))

@[simp] theorem triplePoint_degree (v : Fin 3 ≃ D.a) (x y z : ℕ) :
    D.coreDegree (D.triplePoint v x y z)=x+y+z := by
  simp [triplePoint,coreDegree,coreGeneratorPoint,internalVariable]
@[simp] theorem triplePoint_offset (v : Fin 3 ≃ D.a) (x y z : ℕ) :
    D.coreOffset (D.triplePoint v x y z)=x*(v 0).val+y*(v 1).val+z*(v 2).val := by
  simp [triplePoint,coreOffset,coreGeneratorPoint,internalVariable]
theorem triplePoint_coe (v : Fin 3 ≃ D.a) (x y z : ℕ) :
    (D.triplePoint v x y z).val=(x+y+z,x*(v 0).val+y*(v 1).val+z*(v 2).val) := by
  exact Prod.ext (D.triplePoint_degree v x y z) (D.triplePoint_offset v x y z)

theorem triple_internalPoint (v : Fin 3 ≃ D.a) (β : D.a →₀ ℕ) :
    D.internalPoint β=D.triplePoint v (β (v 0)) (β (v 1)) (β (v 2)) := by
  have hs (f : D.a → ℕ) : ∑ b : D.a,f b=f (v 0)+f (v 1)+f (v 2) := by
    rw [←v.sum_comp f]
    simp [Fin.sum_univ_succ,add_assoc]
  apply Subtype.ext
  apply Prod.ext
  · change D.coreDegree (D.internalPoint β)=_
    rw [D.internalPoint_degree,hs]
    exact (D.triplePoint_degree v _ _ _).symm
  · change D.coreOffset (D.internalPoint β)=_
    rw [D.internalPoint_offset,hs]
    exact (D.triplePoint_offset v _ _ _).symm

theorem triple_internal_offsets (v : Fin 3 ≃ D.a) : D.a={(v 0).val,(v 1).val,(v 2).val} := by
  ext a
  constructor
  · intro ha
    obtain ⟨i,hi⟩ := v.surjective ⟨a,ha⟩
    have hv := congrArg Subtype.val hi
    simp only [Finset.mem_insert,Finset.mem_singleton]
    fin_cases i
    · exact Or.inl hv.symm
    · exact Or.inr (Or.inl hv.symm)
    · exact Or.inr (Or.inr hv.symm)
  · intro ha
    simp only [Finset.mem_insert,Finset.mem_singleton] at ha
    rcases ha with h|h|h <;> rw [h] <;> exact (v _).property

/-- Degree one in the actual generator monoid means an actual offset. -/
theorem degree_one_core_offset (p : D.corePoints) (hp : D.coreDegree p=1) : D.coreOffset p∈D.offsets := by
  obtain ⟨w,hw⟩ := D.exists_coreWord p
  have hd := D.coreWord_degree w
  rw [hw,hp] at hd
  obtain ⟨b,hb⟩ := List.length_eq_one_iff.mp hd.symm
  rw [←hw,hb]
  exact b.property

/-- Both endpoint factors are excluded in the original orientation. -/
theorem degree_two_minimal_of_missing (p : D.corePoints) (hp : D.coreDegree p=2)
    (h0 : D.coreOffset p∉D.offsets)
    (hu : D.coreOffset p<D.u ∨ D.coreOffset p-D.u∉D.offsets) : D.CoreMinimal p := by
  by_contra hm
  rcases (D.core_not_minimal_iff_factor p).mp hm with ⟨q,hq⟩|⟨q,hq⟩
  all_goals
    have hd := congrArg D.coreDegree hq
    have ho := congrArg D.coreOffset hq
    rw [hp,map_add] at hd
    have hqd : D.coreDegree q=1 := by change 2=D.coreDegree q+1 at hd; omega
    have hb := D.degree_one_core_offset q hqd
  · apply h0
    have he : D.coreOffset p=D.coreOffset q := by change D.coreOffset p=D.coreOffset q+0 at ho; omega
    exact he ▸ hb
  · have he : D.coreOffset p=D.coreOffset q+D.u := by
      change D.coreOffset p=D.coreOffset q+D.u at ho
      exact ho
    rcases hu with hu|hu
    · omega
    · apply hu
      have he' : D.coreOffset p-D.u=D.coreOffset q := by omega
      exact he' ▸ hb
end NSP14.Endpoint.Data
