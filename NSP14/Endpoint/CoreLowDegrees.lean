module
public import NSP14.Endpoint.CoreGrading
public import NSP14.Endpoint.CoreInternalPresentation
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open scoped Classical
namespace NSP14.Endpoint.Data
variable (D : NSP14.Endpoint.Data)

theorem coreCoordinates_internal_generator (b : D.a) :
    D.coreCoordinates (D.coreGeneratorPoint (D.internalVariable b))=(⟨b.val,D.a_lt b.val b.property⟩,0,0) := by
  apply D.decodeCoordinate_injective
  rw [D.decode_coreCoordinates]
  have hb : b.val≠0 := Nat.ne_of_gt (D.a_pos b.val b.property)
  apply Prod.ext <;> simp [coreGeneratorPoint,internalVariable,decodeCoordinate,epsilon,hb]

theorem internal_generator_minimal (b : D.a) : D.CoreMinimal (D.coreGeneratorPoint (D.internalVariable b)) := by
  have hm := D.coordinate_mem_fiber (D.coreGeneratorPoint (D.internalVariable b))
  rw [D.coreCoordinates_internal_generator] at hm
  change Minimal (·∈D.coreFiber (D.coreCoordinates _).1) (D.coreCoordinates _).2
  rw [D.coreCoordinates_internal_generator]
  exact ⟨hm,fun _ _ _ => bot_le⟩

def internalMinimalIndex (b : D.a) : D.CoreMinimalIndex :=
  ⟨D.coreGeneratorPoint (D.internalVariable b),D.internal_generator_minimal b⟩

theorem internalMinimalIndex_injective : Function.Injective D.internalMinimalIndex := by
  intro a b h
  apply Subtype.ext
  exact congrArg (fun p : D.CoreMinimalIndex => p.val.val.2) h

theorem core_degree_zero_iff (p : D.corePoints) : D.coreDegree p=0 ↔ p=0 := by
  constructor
  · intro h
    have hb := D.corePoint_bound p.property
    change p.val.2≤D.u*p.val.1 at hb
    change p.val.1=0 at h
    apply Subtype.ext
    apply Prod.ext
    · exact h
    · change p.val.2=0
      rw [h,mul_zero] at hb
      omega
  · rintro rfl
    rfl

theorem coreZero_minimal : D.CoreMinimal 0 := by
  have hcoord : D.coreCoordinates 0=(⟨0,D.u_pos⟩,0,0) := by
    apply D.decodeCoordinate_injective
    rw [D.decode_coreCoordinates]
    simp only [decodeCoordinate,epsilon,ite_true,Nat.zero_add,mul_zero]
    rfl
  change Minimal (·∈D.coreFiber (D.coreCoordinates 0).1) (D.coreCoordinates 0).2
  rw [hcoord]
  exact ⟨D.coreFiber_zero (0,0),fun _ _ _ => bot_le⟩

def zeroMinimalIndex : D.CoreMinimalIndex := ⟨0,D.coreZero_minimal⟩

theorem core_degree_one_internal (p : D.CoreMinimalIndex) (hp : D.coreDegree p.val=1) :
    ∃ b : D.a,D.internalMinimalIndex b=p := by
  obtain ⟨w,hw⟩ := D.exists_coreWord p.val
  have hlen := D.coreWord_degree w
  rw [hw,hp] at hlen
  obtain ⟨b,hb⟩ := List.length_eq_one_iff.mp hlen.symm
  have hm : Minimal (·∈D.coreFiber (D.coreCoordinates (D.coreWord w)).1)
      (D.coreCoordinates (D.coreWord w)).2 := by rw [hw];exact p.property
  have hint := D.minimal_word_internal w hm b (by simp [hb])
  refine ⟨⟨b.val,hint⟩,?_⟩
  apply Subtype.ext
  rw [←hw,hb]
  change D.coreGeneratorPoint (D.internalVariable ⟨b.val,hint⟩)=D.coreGeneratorPoint b+0
  rw [add_zero]
  rfl

noncomputable def internalDegreeOneEquiv : D.a ≃ {p : D.CoreMinimalIndex // D.QCoreDegree p=1} :=
  Equiv.ofBijective (fun b => ⟨D.internalMinimalIndex b,rfl⟩) ⟨by
    intro a b h
    exact D.internalMinimalIndex_injective (congrArg Subtype.val h),by
    intro p
    have hp : D.coreDegree p.val.val=1 := by
      have h : (D.coreDegree p.val.val : ℤ)=1 := p.property
      exact_mod_cast h
    obtain ⟨b,hb⟩ := D.core_degree_one_internal p.val hp
    exact ⟨b,Subtype.ext hb⟩⟩
end NSP14.Endpoint.Data
