module
public import NSP14.Additive.EndpointDistance
@[expose] public section
open scoped Pointwise
namespace NSP14.Additive
theorem threePoint_growth {u : ℕ} [NeZero u] (A : Finset (ZMod u))
    (h0 : 0 ∈ A) (hc : A.card = 3)
    (hgen : AddSubgroup.closure (A : Set (ZMod u)) = ⊤) (n : ℕ) :
    min u (2*n+1) ≤ (iteratedSum A n).card := by
  by_cases hn : n = 0
  · subst n
    simp only [iteratedSum_zero,Finset.card_singleton,mul_zero,zero_add]
    exact min_le_right _ _
  · have hh := generated_sum_growth A h0 hgen n (by omega)
    rw [ZMod.card,hc] at hh
    norm_num only [Nat.reduceAdd,Nat.reduceDiv] at hh
    have he : 3+(n-1)*2=2*n+1 := by omega
    rwa [he] at hh

/-- Collective gcd is sufficient; neither a nor b need be a unit. The
auxiliary endpoint data only supplies the already-proved reachability lemma. -/
theorem threePoint_coprime_growth (u a b : ℕ) (ha : 0 < a) (hab : a < b) (hb : b < u)
    (hg : Nat.gcd (Nat.gcd a b) u = 1) (n : ℕ) :
    min u (2*n+1) ≤ (iteratedSum ({0,(a : ZMod u),(b : ZMod u)} : Finset (ZMod u)) n).card := by
  let : NeZero u := ⟨by omega⟩
  have hne : a ∉ ({b} : Finset ℕ) := by
    simpa only [Finset.mem_singleton] using Nat.ne_of_lt hab
  have hcardab : ({a,b} : Finset ℕ).card=2 := by
    rw [Finset.card_insert_of_notMem hne,Finset.card_singleton]
  let D : NSP14.Endpoint.Data := {
    m := u+1, d := 1, u := u, a := {a,b},
    q_two := hcardab.ge,
    a_pos := by intro x hx; simp only [Finset.mem_insert,Finset.mem_singleton] at hx; rcases hx with rfl|rfl <;> omega,
    a_lt := by intro x hx; simp only [Finset.mem_insert,Finset.mem_singleton] at hx; rcases hx with rfl|rfl <;> omega,
    u_lt := Nat.lt_succ_self u, d_pos := le_rfl,
    offsets_coprime := by simpa only [Finset.gcd_insert,Finset.gcd_singleton,id_eq,
      normalize_eq, gcd_eq_nat_gcd] using hg,
    coprime := Nat.coprime_one_right _ }
  have he : D.residueAlphabet = {0,(a : ZMod u),(b : ZMod u)} := by
    simp [NSP14.Endpoint.Data.residueAlphabet,D]
  have hcard : D.residueAlphabet.card=3 := by
    rw [D.residueAlphabet_card]
    change ({a,b} : Finset ℕ).card+1=3
    rw [hcardab]
  have hh := threePoint_growth D.residueAlphabet D.zero_mem_residueAlphabet hcard D.residueAlphabet_generates n
  rwa [he] at hh
end NSP14.Additive
