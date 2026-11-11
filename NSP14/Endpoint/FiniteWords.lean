module
public import NSP14.Endpoint.SocleCorners
public import NSP14.Endpoint.SurvivingBasis
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open scoped Classical
namespace NSP14.Endpoint.Data
variable (D : Data)

/-- Executable finite sums of actual offsets, at one fixed word length. -/
def offsetSums (D : Data) : ℕ → Finset ℕ
  | 0 => {0}
  | n+1 => D.offsets.biUnion (fun b => (offsetSums D n).image (fun B => b+B))

theorem coreWord_offsetSums (w : List D.Variables) : D.coreOffset (D.coreWord w)∈D.offsetSums w.length := by
  induction w with
  | nil => simp [offsetSums,coreWord_nil]
  | cons b w ih =>
    simp only [List.length_cons,offsetSums,Finset.mem_biUnion,Finset.mem_image]
    refine ⟨b.val,b.property,D.coreOffset (D.coreWord w),ih,?_⟩
    rw [D.coreWord_cons,(D.coreOffset).map_add]
    rfl

theorem offsetSums_core (n B : ℕ) (hB : B∈D.offsetSums n) : (n,B)∈D.corePoints := by
  induction n generalizing B with
  | zero =>
    have he : B=0 := by simpa [offsetSums] using hB
    subst B
    exact D.corePoints.zero_mem
  | succ n ih =>
    obtain ⟨b,hb,himage⟩ := Finset.mem_biUnion.mp hB
    obtain ⟨A,hA,hAB⟩ := Finset.mem_image.mp himage
    have h := D.corePoints.add_mem (D.coreGeneratorPoint ⟨b,hb⟩).property (ih A hA)
    change (n+1,B)∈D.corePoints
    convert h using 1; simp [coreGeneratorPoint,hAB,Nat.add_comm]

theorem corePoint_iff_offsetSums (n B : ℕ) : (n,B)∈D.corePoints ↔ B∈D.offsetSums n := by
  constructor
  · intro hp
    let p : D.corePoints := ⟨(n,B),hp⟩
    obtain ⟨w,hw⟩ := D.exists_coreWord p
    have hlen := D.coreWord_degree w
    have hB := D.coreWord_offsetSums w
    rw [hw] at hlen hB
    change B∈D.offsetSums n
    change B∈D.offsetSums w.length at hB
    change n=w.length at hlen
    exact hlen ▸ hB
  · exact D.offsetSums_core n B
end NSP14.Endpoint.Data
