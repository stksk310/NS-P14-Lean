module
public import NSP14.Endpoint.Fibers
@[expose] public section
namespace NSP14.Endpoint.Data
variable (D : NSP14.Endpoint.Data)

def coreWord (w : List D.Variables) : D.corePoints := (w.map D.coreGeneratorPoint).sum

@[simp] theorem coreWord_nil : D.coreWord []=0 := rfl

theorem coreWord_cons (b : D.Variables) (w : List D.Variables) :
    D.coreWord (b::w)=D.coreGeneratorPoint b+D.coreWord w := rfl

theorem coreWord_append (w z : List D.Variables) : D.coreWord (w++z)=D.coreWord w+D.coreWord z := by
  simp only [coreWord,List.map_append,List.sum_append]

theorem coreWord_degree (w : List D.Variables) : D.coreDegree (D.coreWord w)=w.length := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    rw [D.coreWord_cons,(D.coreDegree).map_add]
    change 1+D.coreDegree (D.coreWord w)=List.length (b::w)
    rw [ih,List.length_cons]
    omega

theorem coreWord_offset (w : List D.Variables) : D.coreOffset (D.coreWord w)=(w.map Subtype.val).sum := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    rw [D.coreWord_cons,(D.coreOffset).map_add]
    change b.val+D.coreOffset (D.coreWord w)=b.val+(w.map Subtype.val).sum
    rw [ih]

/-- Closure membership supplies a genuine word in the same generator
monoid, not merely a degree/offset bound. -/
theorem exists_coreWord (p : D.corePoints) : ∃ w : List D.Variables,D.coreWord w=p := by
  have h : ∃ w : List D.Variables,(D.coreWord w).val=p.val := by
    apply AddSubmonoid.closure_induction (motive:=fun a _ => ∃ w : List D.Variables,(D.coreWord w).val=a) ?_ ?_ ?_ p.property
    · rintro a ⟨b,rfl⟩
      exact ⟨[b],by simp only [coreWord,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero];rfl⟩
    · exact ⟨[],rfl⟩
    · rintro a b _ _ ⟨w,hw⟩ ⟨z,hz⟩
      refine ⟨w++z,?_⟩
      rw [D.coreWord_append]
      change (D.coreWord w).val+(D.coreWord z).val=a+b
      rw [hw,hz]
  obtain ⟨w,hw⟩ := h
  exact ⟨w,Subtype.ext hw⟩
end NSP14.Endpoint.Data
