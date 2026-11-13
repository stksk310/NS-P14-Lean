module
public import NSP14.Additive.CyclicAntipodal
public import NSP14.Additive.ThreePointGrowth
@[expose] public section
open scoped Pointwise Classical
open NSP14.Additive
namespace Run17Growth
def A6 : Finset (ZMod 6) := {0,2,3}
def anti8 : Finset (ZMod 8) := {0,1,4,5}
def plain8 : Finset (ZMod 8) := {0,1,2,4}
theorem A6_layers : (iteratedSum A6 0).card=1 ∧ (iteratedSum A6 1).card=3 ∧
    (iteratedSum A6 2).card=5 ∧ (iteratedSum A6 3).card=6 := by decide
theorem A6_all_n (n : ℕ) : min 6 (2*n+1) ≤ (iteratedSum A6 n).card :=
  threePoint_coprime_growth 6 2 3 (by decide) (by decide) (by decide) (by decide) n
theorem antipodal_increment : (iteratedSum anti8 2).card=(iteratedSum anti8 1).card+2 := by decide
theorem plain_increment : (iteratedSum plain8 2).card=(iteratedSum plain8 1).card+3 := by decide
theorem both_proper : iteratedSum anti8 2 ≠ Finset.univ ∧ iteratedSum plain8 2 ≠ Finset.univ := by decide
theorem antipodal_form : CyclicAntipodal 8 anti8 := ⟨4,1,by decide,by decide,by decide,by decide,rfl⟩
theorem plain_nonantipodal : ¬CyclicAntipodal 8 plain8 := by
  rintro ⟨h,t,hu,ht0,hth,_,he⟩
  have hh : h=4 := by omega
  subst h
  have ht : t=1 ∨ t=2 ∨ t=3 := by omega
  rcases ht with rfl | rfl | rfl
  · exact (show plain8 ≠ {0,(1 : ZMod 8),4,(1+4 : ZMod 8)} from by decide) he
  · exact (show plain8 ≠ {0,(2 : ZMod 8),4,(2+4 : ZMod 8)} from by decide) he
  · exact (show plain8 ≠ {0,(3 : ZMod 8),4,(3+4 : ZMod 8)} from by decide) he
theorem plain_all_n (n : ℕ) : min 8 (3*n+1) ≤ (iteratedSum plain8 n).card :=
  fourPoint_growth plain8 (by decide) (by decide)
    (zmod_generates_of_one_mem plain8 (by decide)) plain_nonantipodal n
theorem odd_even_ceiling : (3+1)/2=2 ∧ (4+1)/2=2 ∧ (5+1)/2=3 ∧ (6+1)/2=3 := by decide
theorem saturated8 : iteratedSum anti8 3=Finset.univ ∧ iteratedSum plain8 3=Finset.univ := by decide
theorem whole_stabilizer : sumStabilizer (Finset.univ : Finset (ZMod 8))=⊤ := by
  unfold sumStabilizer
  simp only [Finset.coe_univ,AddAction.stabilizer_univ]
end Run17Growth
