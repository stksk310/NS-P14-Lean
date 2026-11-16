module
public import NSP14.ArithmeticSequence.Source
@[expose] public section
open scoped Classical
namespace NSP14.ArithmeticSequence

/-- The AP underlying an interval; its genuine minimal list stops at 2m−1. -/
def intervalData (m w : ℕ) (hm : 2 ≤ m) (hw : 1 ≤ w) : Data where
  m := m
  d := 1
  v := min w (m-1)
  m_two := hm
  d_pos := le_rfl
  v_pos := le_min hw (by omega)
  v_lt := (min_le_right _ _).trans_lt (by omega)
  coprime := Nat.coprime_one_right _

/-- The redundant generators at and above 2m are removed by actual additive
closure, rather than by merely substituting a truncated numerical profile. -/
theorem interval_closure (m w : ℕ) (hm : 2 ≤ m) (hw : 1 ≤ w) :
    AddSubmonoid.closure (Set.Icc m (m+w))=(intervalData m w hm hw).source.carrier := by
  let D := intervalData m w hm hw
  apply le_antisymm
  · apply AddSubmonoid.closure_le.mpr
    suffices h : ∀ n, n ∈ Set.Icc m (m+w) → n ∈ D.source from h
    intro n
    induction n using Nat.strong_induction_on with
    | ind n ih =>
      rintro ⟨hn,hnw⟩
      by_cases ht : n < 2*m
      · have hv : n-m ≤ D.v := by
          change n-m ≤ min w (m-1)
          omega
        have he : n=m+(n-m)*D.d := by change n=m+(n-m)*1;omega
        rw [he]
        exact D.generator_mem _ hv
      · have hp : n-m < n := by omega
        have hn' : n-m ∈ Set.Icc m (m+w) := by constructor <;> omega
        have hc := D.source.add_mem (D.generator_mem 0 (by omega)) (ih (n-m) hp hn')
        change m+0*1+(n-m) ∈ D.source at hc
        simpa only [Nat.zero_mul,Nat.add_zero,Nat.add_sub_of_le hn] using hc
  · rw [← D.source.closure_atoms]
    apply AddSubmonoid.closure_mono
    intro n hn
    obtain ⟨i,hi,he⟩ := D.atom_eq_generator ((D.source.mem_atoms_iff _).mp hn)
    have hiv : i ≤ w := hi.trans (min_le_left _ _)
    change n=m+i*1 at he
    constructor <;> omega
end NSP14.ArithmeticSequence
