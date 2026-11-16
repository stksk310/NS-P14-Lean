module
public import NSP14.Width.FiveHoleCore
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open scoped Classical
namespace NSP14.Endpoint.Data
variable (D : NSP14.Endpoint.Data)

theorem fiveHole_classification (hq : D.q=3) (hu : D.u=5) :
    D.a={1,2,3} ∨ D.a={1,2,4} ∨ D.a={1,3,4} ∨ D.a={2,3,4} := by
  have hs : D.a⊆({1,2,3,4}:Finset ℕ) := by
    intro b hb
    have hp := D.a_pos b hb
    have hl := D.a_lt b hb
    rw [hu] at hl
    simp only [Finset.mem_insert,Finset.mem_singleton]
    omega
  have hm : D.a∈({1,2,3,4}:Finset ℕ).powersetCard 3 :=
    Finset.mem_powersetCard.mpr ⟨hs,hq⟩
  have ht : ({1,2,3,4}:Finset ℕ).powersetCard 3={{1,2,3},{1,2,4},{1,3,4},{2,3,4}} := by decide
  simpa only [ht,Finset.mem_insert,Finset.mem_singleton] using hm

noncomputable def fiveHoleVariableEquiv (flip : Bool)
    (ha : D.a=if flip then {1,2,4} else {1,3,4}) : Fin 3 ≃ D.a :=
  Equiv.ofBijective (fun i => ⟨fiveHoleValues flip i,by
    rw [ha]
    cases flip <;> fin_cases i <;> norm_num [fiveHoleValues]⟩) (by
    constructor
    · intro i j he
      have hv := congrArg Subtype.val he
      cases flip <;> fin_cases i <;> fin_cases j <;> norm_num [fiveHoleValues] at hv <;> rfl
    · intro b
      have hb := (congrArg (fun s : Finset ℕ => b.val∈s) ha).mp b.property
      cases flip
      · simp only [Bool.false_eq_true,ite_false,Finset.mem_insert,Finset.mem_singleton] at hb
        rcases hb with hb|hb|hb
        · exact ⟨0,Subtype.ext (by simpa [fiveHoleValues] using hb.symm)⟩
        · exact ⟨1,Subtype.ext (by simpa [fiveHoleValues] using hb.symm)⟩
        · exact ⟨2,Subtype.ext (by simpa [fiveHoleValues] using hb.symm)⟩
      · simp only [ite_true,Finset.mem_insert,Finset.mem_singleton] at hb
        rcases hb with hb|hb|hb
        · exact ⟨1,Subtype.ext (by simpa [fiveHoleValues] using hb.symm)⟩
        · exact ⟨2,Subtype.ext (by simpa [fiveHoleValues] using hb.symm)⟩
        · exact ⟨0,Subtype.ext (by simpa [fiveHoleValues] using hb.symm)⟩)

theorem fiveHoleVariableEquiv_val (flip : Bool)
    (ha : D.a=if flip then {1,2,4} else {1,3,4}) (i : Fin 3) :
    (D.fiveHoleVariableEquiv flip ha i).val=fiveHoleValues flip i := rfl
end NSP14.Endpoint.Data
