module
public import NSP14.Endpoint.Antichains
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open scoped Classical
namespace NSP14.Endpoint

/-- A simultaneous x/v annihilator label in a monomial quotient. -/
def Corner (U : Set (ℕ×ℕ)) (c : ℕ×ℕ) : Prop :=
  c∉U ∧ (c.1+1,c.2)∈U ∧ (c.1,c.2+1)∈U

variable (U : Set (ℕ×ℕ)) (hU : ∀ {a b},a∈U → a≤b → b∈U)

include hU in
theorem corner_eq_of_fst {a b : ℕ×ℕ} (ha : Corner U a) (hb : Corner U b) (he : a.1=b.1) : a=b := by
  apply Prod.ext he
  by_contra hK
  rcases lt_or_gt_of_ne hK with hlt|hgt
  · exact hb.1 (hU ha.2.2 ⟨he.le,by omega⟩)
  · exact ha.1 (hU hb.2.2 ⟨he.ge,by omega⟩)

noncomputable def cornerRight (c : {c | Corner U c}) : {b | Minimal (·∈U) b} :=
  let h := exists_minimal_le_of_wellFoundedLT (·∈U) (c.val.1+1,c.val.2) c.property.2.1
  ⟨h.choose,h.choose_spec.2⟩

include hU in
theorem cornerRight_fst (c : {c | Corner U c}) : (cornerRight U c).val.1=c.val.1+1 := by
  have hle := (exists_minimal_le_of_wellFoundedLT (·∈U) (c.val.1+1,c.val.2) c.property.2.1).choose_spec.1
  change (cornerRight U c).val≤(c.val.1+1,c.val.2) at hle
  have hb := (cornerRight U c).property.prop
  by_contra he
  have hc := hU hb (show (cornerRight U c).val≤c.val from ⟨by have := hle.1;omega,hle.2⟩)
  exact c.property.1 hc

include hU in
theorem cornerRight_injective : Function.Injective (cornerRight U) := by
  intro a b h
  apply Subtype.ext
  apply corner_eq_of_fst U hU a.property b.property
  have hf := congrArg (fun b : {b | Minimal (·∈U) b} => b.val.1) h
  rw [cornerRight_fst U hU,cornerRight_fst U hU] at hf
  omega

variable (c : ℕ×ℕ) (hc : c∈U)

include hU c hc in
theorem corner_finite : Set.Finite {a | Corner U a} := by
  have : Finite {b | Minimal (·∈U) b} := (minimal_finite_of_mem U c hc).to_subtype
  have : Finite {a | Corner U a} := Finite.of_injective (cornerRight U) (cornerRight_injective U hU)
  exact Set.toFinite _

include hU c hc in
theorem corner_card_lt_minimal : Nat.card {a | Corner U a}<Nat.card {b | Minimal (·∈U) b} := by
  have : Finite {b | Minimal (·∈U) b} := (minimal_finite_of_mem U c hc).to_subtype
  have : Finite {a | Corner U a} := (corner_finite U hU c hc).to_subtype
  let P (n : ℕ) := ∃ a : ℕ×ℕ,a∈U ∧ a.1=n
  have hex : ∃ n,P n := ⟨c.1,c,hc,rfl⟩
  obtain ⟨a,ha,haL⟩ := Nat.find_spec hex
  obtain ⟨b,hba,hb⟩ := exists_minimal_le_of_wellFoundedLT (·∈U) a ha
  have hminL : ∀ z∈U,b.1≤z.1 := by
    intro z hz
    have hn := Nat.find_min' hex (show P z.1 from ⟨z,hz,rfl⟩)
    have hL := hba.1
    omega
  have hnot : ¬Function.Surjective (cornerRight U) := by
    intro hs
    obtain ⟨z,hz⟩ := hs ⟨b,hb⟩
    have hL := cornerRight_fst U hU z
    have hlow := hminL (z.val.1,z.val.2+1) z.property.2.2
    rw [hz] at hL
    change b.1=z.val.1+1 at hL
    omega
  let : Fintype {a | Corner U a} := Fintype.ofFinite _
  let : Fintype {b | Minimal (·∈U) b} := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card,Nat.card_eq_fintype_card]
  exact Fintype.card_lt_of_injective_not_surjective _ (cornerRight_injective U hU) hnot
end NSP14.Endpoint
