module
public import NSP14.Semigroup.IntervalCompletionAll
public import NSP14.Semigroup.CarrierTransport
public import NSP14.Semigroup.WidthNormalization
public import NSP14.Semigroup.RegularHeadBetti
public import NSP14.Target.APLowerRows
@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000
open scoped Classical
open NSP14.Homological
namespace NSP14.SmallEmbedding
variable (S : NumericalSemigroup)

/-- One atom must be 1, by actual cofiniteness, not by a chosen presentation. -/
theorem one_atom (he : S.embeddingDimension=1) :
    S.atoms={1} ∧ S.multiplicity=1 ∧ S.maxAtom=1 ∧ S.carrier=⊤ := by
  have hc : S.atoms.card=1 := he
  obtain ⟨a,ha⟩ := Finset.card_eq_one.mp hc
  have hg := S.atoms_gcd_one
  have ha1 : a=1 := by simpa [ha] using hg
  have hset : S.atoms={1} := by simpa only [ha1] using ha
  have hm : S.multiplicity=1 := by
    have h := S.multiplicity_mem_atoms
    simpa only [hset,Finset.mem_singleton] using h
  have hmax : S.maxAtom=1 := by
    have h : S.maxAtom∈S.atoms := Finset.max'_mem S.atoms ⟨S.multiplicity,S.multiplicity_mem_atoms⟩
    rwa [hset,Finset.mem_singleton] at h
  have htop : S.carrier=⊤ := by
    apply top_unique
    intro n hn
    clear hn
    have h1 : 1∈S.carrier := by
      change 1∈S
      rw [←hm]
      exact S.multiplicity_mem
    induction n with
    | zero => exact S.carrier.zero_mem
    | succ n ih => exact S.carrier.add_mem ih h1
  exact ⟨hset,hm,hmax,htop⟩

theorem one_literal_carrier (he : S.embeddingDimension=1) :
    S.carrier=S.intervalCompletionAll.carrier := by
  have ht := (one_atom S he).2.2.2
  apply le_antisymm S.le_literal_interval
  rw [ht]
  exact le_top

theorem one_order (he : S.embeddingDimension=1) (n : ℕ) : S.order n=n := by
  have hm := (one_atom S he).2.1
  have ht := (one_atom S he).2.2.2
  have hn (n : ℕ) : n∈S := by change n∈S.carrier;rw [ht];trivial
  induction n with
  | zero => exact S.order_zero
  | succ n ih =>
    have hu := S.order_bound (hn (n+1))
    have hl := S.order_add_multiplicity (hn n)
    rw [hm,mul_one] at hu
    rw [hm,ih] at hl
    omega

theorem one_x_regular (he : S.embeddingDimension=1) (k : Type) [Field k] :
    Function.Injective (S.xMultiply k) := by
  have hm := (one_atom S he).2.1
  have hn (x : ℕ) : ¬S.Terminal x := by
    intro h
    have ht := h.2
    rw [one_order S he,one_order S he,hm] at ht
    omega
  have : IsEmpty S.TerminalExponent := ⟨fun x => hn x.val.val x.property⟩
  have : Subsingleton (S.TerminalExponent →₀ k) := inferInstance
  have : Subsingleton (S.xMultiply k).ker := (S.xKernelEquiv k).injective.subsingleton
  apply LinearMap.ker_eq_bot.mp
  apply bot_unique
  intro a ha
  change a=0
  have h : (⟨a,ha⟩ : (S.xMultiply k).ker)=0 := Subsingleton.elim _ _
  exact congrArg Subtype.val h

/-- Actual completed one-generator Betti sequence, including its zero row. -/
theorem one_completed_betti (he : S.embeddingDimension=1) (k : Type) [Field k] (i : ℕ) :
    totalBetti k S.AtomExponent
      (ModuleCat.of (S.FullPolynomialRing k) (S.FormalTangentAlgebra k)) i=if i=0 then 1 else 0 := by
  by_cases hi : i=0
  · subst i;rw [S.completed_totalBetti_zero k];rfl
  rw [ite_eq_right hi,←S.completed_totalBetti k,S.xRegular_totalBetti k (one_x_regular S he k)]
  apply totalBetti_eq_zero_of_gt
  rw [S.nonXAtom_card,he]
  omega

/-- The two actual atoms are m<n, and their AP difference is coprime to m. -/
theorem two_atoms (he : S.embeddingDimension=2) :
    ∃ n : ℕ, S.multiplicity<n ∧ S.atoms={S.multiplicity,n} ∧ Nat.Coprime S.multiplicity (n-S.multiplicity) := by
  have hc : (S.atoms.erase S.multiplicity).card=1 := by rw [S.nonmultiplicity_atoms_card,he]
  obtain ⟨n,hn⟩ := Finset.card_eq_one.mp hc
  have hmem : n∈S.atoms.erase S.multiplicity := by rw [hn];exact Finset.mem_singleton_self _
  have hat := (S.mem_atoms_iff _).mp (Finset.mem_erase.mp hmem).2
  have hmin := S.multiplicity_le hat.1 hat.2.1
  have hlt : S.multiplicity<n := by have := (Finset.mem_erase.mp hmem).1;omega
  have hset : S.atoms={S.multiplicity,n} := by
    rw [←hn,Finset.insert_erase S.multiplicity_mem_atoms]
  have hcop : Nat.Coprime S.multiplicity n := by
    have h := S.atoms_gcd_one
    simpa [hset,gcd_eq_nat_gcd] using h
  exact ⟨n,hlt,hset,(Nat.coprime_sub_self_right hlt.le).mpr hcop⟩

noncomputable def twoAP (he : S.embeddingDimension=2) : ArithmeticSequence.Data where
  m := S.multiplicity
  d := (two_atoms S he).choose-S.multiplicity
  v := 1
  m_two := by have h := S.embeddingDimension_le_multiplicity;omega
  d_pos := by have h := (two_atoms S he).choose_spec.1;omega
  v_pos := by omega
  v_lt := by have h := S.embeddingDimension_le_multiplicity;omega
  coprime := (two_atoms S he).choose_spec.2.2

theorem twoAP_carrier (he : S.embeddingDimension=2) : S.carrier=(twoAP S he).source.carrier := by
  let A := twoAP S he
  let n := (two_atoms S he).choose
  have hlt : S.multiplicity<n := (two_atoms S he).choose_spec.1
  have hset : S.atoms={S.multiplicity,n} := (two_atoms S he).choose_spec.2.1
  have hm : A.m=S.multiplicity := rfl
  have hgen : ∀ j : ℕ,j ≤ 1 → A.m+j*A.d∈S.atoms := by
    intro j hj
    have hj' : j=0 ∨ j=1 := by omega
    rcases hj' with rfl|rfl
    · simpa only [hm,zero_mul,add_zero] using S.multiplicity_mem_atoms
    · have heq : A.m+1*A.d=n := by change S.multiplicity+1*(n-S.multiplicity)=n;omega
      rw [heq,hset]
      exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  rw [←S.closure_atoms,←A.source.closure_atoms]
  congr 1
  apply Set.ext
  intro x
  constructor
  · intro hx
    change x∈S.atoms at hx
    have hx' : x=S.multiplicity ∨ x=n := by simpa only [hset,Finset.mem_insert,Finset.mem_singleton] using hx
    rcases hx' with rfl|rfl
    · have hg := A.generator_atom 0 (by change 0 ≤ 1;omega)
      rw [hm,zero_mul,add_zero] at hg
      exact (A.source.mem_atoms_iff _).mpr hg
    · have hg := A.generator_atom 1 (by change 1 ≤ 1;omega)
      have heq : A.m+1*A.d=n := by change S.multiplicity+1*(n-S.multiplicity)=n;omega
      rw [heq] at hg
      exact (A.source.mem_atoms_iff _).mpr hg
  · intro hx
    obtain ⟨j,hj,rfl⟩ := A.atom_eq_generator ((A.source.mem_atoms_iff _).mp hx)
    exact hgen j hj

/-- The existing actual two-generator AP resolution supplies all quotient rows. -/
theorem two_completed_betti (he : S.embeddingDimension=2) (k : Type) [Field k] (i : ℕ) :
    totalBetti k S.AtomExponent
      (ModuleCat.of (S.FullPolynomialRing k) (S.FormalTangentAlgebra k)) i=
        if i=0 then 1 else if i=1 then 1 else 0 := by
  by_cases hi : i=0
  · subst i;rw [S.completed_totalBetti_zero k];rfl
  rw [ite_eq_right hi,←S.completed_totalBetti k,
    S.carrier_totalBetti _ (twoAP_carrier S he) k i,
    (twoAP S he).cone_totalBetti_pos k i (by omega),
    (twoAP S he).positiveBettiProfile_v_one rfl i (by omega)]

/-- All base comparisons use the unconditional literal interval, including width zero. -/
theorem base_comparison (k : Type) [Field k] (he : S.embeddingDimension ≤ 2) (i : ℕ) :
    totalBetti k S.AtomExponent
      (ModuleCat.of (S.FullPolynomialRing k) (S.FormalTangentAlgebra k)) i ≤
      totalBetti k S.intervalCompletionAll.AtomExponent
        (ModuleCat.of (S.intervalCompletionAll.FullPolynomialRing k)
          (S.intervalCompletionAll.FormalTangentAlgebra k)) i := by
  have hpos := S.embeddingDimension_pos
  by_cases h1 : S.embeddingDimension=1
  · rw [←S.completed_totalBetti k,←S.intervalCompletionAll.completed_totalBetti k,
      S.carrier_totalBetti _ (one_literal_carrier S h1) k i]
  have h2 : S.embeddingDimension=2 := by omega
  by_cases hi0 : i=0
  · subst i;rw [S.completed_totalBetti_zero k,S.intervalCompletionAll.completed_totalBetti_zero k]
  rw [two_completed_betti S h2 k i,ite_eq_right hi0]
  by_cases hi1 : i=1
  · subst i
    rw [ite_eq_left rfl,←S.intervalCompletionAll.completed_totalBetti k,
      S.intervalCompletionAll.carrier_totalBetti (S.intervalCompletion (by omega))
        (S.intervalCompletionAll_carrier_eq (by omega)) k 1,
      (S.intervalCompletion (by omega)).completed_totalBetti k]
    have ht := (S.interval_completed_TLOW k (by omega)).1
    exact (show 1 ≤ (min S.width (S.multiplicity-1)).choose 2+1 by omega).trans ht
  · rw [ite_eq_right hi1]
    exact Nat.zero_le _
end NSP14.SmallEmbedding
