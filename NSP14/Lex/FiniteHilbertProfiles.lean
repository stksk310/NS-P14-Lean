module
public import NSP14.Lex.Uniqueness
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Instances.Discrete
public import Mathlib.Topology.Instances.Nat
@[expose] public section
open scoped Classical
noncomputable section
namespace NSP14.Lex
abbrev MonomialProfile (q : ℕ) := (Fin q →₀ ℕ) → Bool

def ProfileUpper (q : ℕ) (p : MonomialProfile q) : Prop :=
  ∀ a b,a≤b→p a=true→p b=true

def profileHilbert (q : ℕ) (p : MonomialProfile q) (n : ℕ) : ℕ :=
  Fintype.card {a : PolynomialDegreeIndex q n // p a.val=false}

def profileMinimal (q : ℕ) (p : MonomialProfile q) (a : Fin q →₀ ℕ) : Prop :=
  p a=true ∧ ∀ b,b≤a→p b=true→b=a

theorem profileMinimal_finite (q : ℕ) (p : MonomialProfile q) :
    {a | profileMinimal q p a}.Finite := by
  apply WellQuasiOrderedLE.finite_of_isAntichain
  intro a ha b hb hne hle
  exact hne (hb.2 a hle ha.1)

def profileGenerators (q : ℕ) (p : MonomialProfile q) : Finset (Fin q →₀ ℕ) :=
  (profileMinimal_finite q p).toFinset

theorem profile_mem_iff_generator (q : ℕ) (p : MonomialProfile q) (hp : ProfileUpper q p)
    (a : Fin q →₀ ℕ) : p a=true ↔ ∃ b∈profileGenerators q p,b≤a := by
  constructor
  · intro ha
    obtain ⟨b,hba,hb,hmin⟩ := (Set.isPWO_of_wellQuasiOrderedLE {x | p x=true}).exists_le_minimal ha
    refine ⟨b,?_,hba⟩
    change b∈(profileMinimal_finite q p).toFinset
    rw [Set.Finite.mem_toFinset]
    exact ⟨hb,fun c hcb hc => le_antisymm hcb (hmin hc hcb)⟩
  · rintro ⟨b,hb,hba⟩
    have hmin : profileMinimal q p b := (Set.Finite.mem_toFinset _).mp hb
    exact hp b a hba hmin.1

theorem profile_eq_of_le_sameHilbert (q : ℕ) (p r : MonomialProfile q)
    (hle : ∀ a,p a=true → r a=true)
    (hH : ∀ n,profileHilbert q p n=profileHilbert q r n) : p=r := by
  have he (n : ℕ) :
      Finset.univ.filter (fun a : PolynomialDegreeIndex q n => r a.val=false)=
      Finset.univ.filter (fun a : PolynomialDegreeIndex q n => p a.val=false) := by
    apply Finset.eq_of_subset_of_card_le
    · intro a ha
      simp only [Finset.mem_filter,Finset.mem_univ,true_and] at ha ⊢
      cases hpa : p a.val
      · rfl
      · have hr := hle a.val hpa
        simp only [ha] at hr
        contradiction
    · have hc := hH n
      simpa only [profileHilbert,Fintype.card_subtype] using hc.le
  funext a
  have ht : r a=false ↔ p a=false := by
    have hh := congrArg (fun s => (⟨a,rfl⟩ : PolynomialDegreeIndex q a.degree)∈s) (he a.degree)
    simpa only [Finset.mem_filter,Finset.mem_univ,true_and] using Iff.of_eq hh
  cases hp : p a <;> cases hr : r a <;> simp_all
end NSP14.Lex

namespace NSP14.Lex

def hilbertProfiles (q : ℕ) (H : ℕ → ℕ) : Set (MonomialProfile q) :=
  {p | ProfileUpper q p ∧ ∀ n,profileHilbert q p n=H n}

theorem profileHilbert_continuous (q n : ℕ) :
    Continuous (fun p : MonomialProfile q => profileHilbert q p n) := by
  let f : (PolynomialDegreeIndex q n → Bool) → ℕ := fun s => Fintype.card {a // s a=false}
  have hf : Continuous f := continuous_of_discreteTopology
  exact hf.comp (continuous_pi (fun a => continuous_apply a.val))

theorem profileUpper_isClosed (q : ℕ) : IsClosed {p | ProfileUpper q p} := by
  have he : {p | ProfileUpper q p}=(⋂ a,⋂ b,{p : MonomialProfile q | a≤b → p a=true → p b=true}) := by
    ext p
    simp only [ProfileUpper,Set.mem_iInter,Set.mem_ofPred_eq]
  rw [he]
  apply isClosed_iInter
  intro a
  apply isClosed_iInter
  intro b
  by_cases hab : a≤b
  · have he : {p : MonomialProfile q | a≤b → p a=true → p b=true}=
        {p | p a=false} ∪ {p | p b=true} := by
      ext p
      cases ha : p a <;> simp [hab,ha]
    rw [he]
    exact (isClosed_eq (continuous_apply a) continuous_const).union
      (isClosed_eq (continuous_apply b) continuous_const)
  · simpa only [hab,false_implies,Set.ofPred_true] using (isClosed_univ : IsClosed (Set.univ : Set (MonomialProfile q)))

theorem hilbertProfiles_isClosed (q : ℕ) (H : ℕ → ℕ) : IsClosed (hilbertProfiles q H) := by
  have hc : IsClosed (⋂ n,{p : MonomialProfile q | profileHilbert q p n=H n}) :=
    isClosed_iInter (fun n => isClosed_eq (profileHilbert_continuous q n) continuous_const)
  simpa only [hilbertProfiles,Set.ofPred_and,Set.ofPred_forall] using (profileUpper_isClosed q).inter hc

theorem hilbertProfiles_finite (q : ℕ) (H : ℕ → ℕ) : (hilbertProfiles q H).Finite := by
  let X := hilbertProfiles q H
  let : CompactSpace X := isCompact_iff_compactSpace.mp (hilbertProfiles_isClosed q H).isCompact
  let : DiscreteTopology X := discreteTopology_iff_isOpen_singleton.mpr (fun p => by
    let V : Set X := ⋂ b : (profileGenerators q p.val),{r | r.val b.val=true}
    have hV : IsOpen V := isOpen_iInter_of_finite (fun b => by
      have hf : Continuous (fun r : X => r.val b.val) :=
        (continuous_apply b.val).comp continuous_subtype_val
      simpa only [Set.preimage,Set.mem_singleton_iff] using
        (IsOpen.preimage (f:=fun r : X => r.val b.val) hf
          (isOpen_discrete ({true} : Set Bool))))
    have he : V={p} := by
      ext r
      simp only [V,Set.mem_iInter,Set.mem_ofPred_eq,Set.mem_singleton_iff]
      constructor
      · intro hr
        apply Subtype.ext
        symm
        apply profile_eq_of_le_sameHilbert q p.val r.val
        · intro a ha
          obtain ⟨b,hb,hba⟩ := (profile_mem_iff_generator q p.val p.property.1 a).mp ha
          exact r.property.1 b a hba (hr ⟨b,hb⟩)
        · intro n
          exact (p.property.2 n).trans (r.property.2 n).symm
      · rintro rfl b
        exact ((Set.Finite.mem_toFinset _).mp b.property).1
    rwa [he] at hV)
  let : Finite X := finite_of_compact_of_discrete
  exact Set.toFinite X
end NSP14.Lex

namespace NSP14.Lex
variable (k : Type) [Field k] (q : ℕ)
attribute [local instance] MvPolynomial.gradedAlgebra

def monomialIdealProfile (I : Ideal (MvPolynomial (Fin q) k)) : MonomialProfile q :=
  fun a => decide (MvPolynomial.monomial a (1:k)∈I)

theorem monomialIdealProfile_upper (I : Ideal (MvPolynomial (Fin q) k)) :
    ProfileUpper q (monomialIdealProfile k q I) := by
  intro a b hab ha
  simp only [monomialIdealProfile,decide_eq_true_eq] at ha ⊢
  exact monomial_mem_of_le k q I a b ha hab

theorem monomialIdealProfile_hilbert (I : Ideal (MvPolynomial (Fin q) k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin q) k))
    (hmono : IsMonomial k q I) (n : ℕ) :
    profileHilbert q (monomialIdealProfile k q I) n=quotientHilbert k q I hI n := by
  rw [quotientHilbert_eq_standard_card]
  simp only [profileHilbert,monomialIdealProfile,decide_eq_false_iff_not,
    standardExponent_iff_not_mem k q hmono]

theorem monomialIdealProfile_injective :
    Set.InjOn (monomialIdealProfile k q) {I | IsMonomial k q I} := by
  intro I hI J hJ he
  have hm (a : Fin q →₀ ℕ) : MvPolynomial.monomial a (1:k)∈I ↔ MvPolynomial.monomial a (1:k)∈J := by
    have hh := congrArg (fun p : MonomialProfile q => p a=true) he
    simpa only [monomialIdealProfile,decide_eq_true_eq] using Iff.of_eq hh
  rw [hI.span k q,hJ.span k q]
  congr 2
  ext a
  exact hm a

/-- Finitely many actual monomial ideals have a fixed entire quotient Hilbert function.
The quotient need not be Artinian and the coefficient field need not be finite. -/
theorem finite_monomialIdeals_sameHilbert (H : ℕ → ℕ) :
    {I : Ideal (MvPolynomial (Fin q) k) | IsMonomial k q I ∧
      ∃ hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin q) k),
        ∀ n,quotientHilbert k q I hI n=H n}.Finite := by
  let A := {I : Ideal (MvPolynomial (Fin q) k) | IsMonomial k q I ∧
    ∃ hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin q) k),
      ∀ n,quotientHilbert k q I hI n=H n}
  let f : A → hilbertProfiles q H := fun I =>
    ⟨monomialIdealProfile k q I.val,monomialIdealProfile_upper k q I.val,by
      obtain ⟨hI,hH⟩ := I.property.2
      intro n
      exact (monomialIdealProfile_hilbert k q I.val hI I.property.1 n).trans (hH n)⟩
  have hf : Function.Injective f := by
    intro I J he
    apply Subtype.ext
    exact monomialIdealProfile_injective k q I.property.1 J.property.1 (congrArg Subtype.val he)
  let : Finite (hilbertProfiles q H) := (hilbertProfiles_finite q H).to_subtype
  let : Finite A := Finite.of_injective f hf
  exact Set.toFinite A
end NSP14.Lex

namespace NSP14.Lex
attribute [local instance] MvPolynomial.gradedAlgebra
/-- A whole Hilbert function bounds the degrees of minimal monomial generators,
uniformly over coefficient fields. This is a finiteness bound, not a lex existence assertion. -/
theorem uniform_monomialGenerator_degree_bound (q : ℕ) (H : ℕ → ℕ) :
    ∃ B : ℕ,∀ (k : Type) [Field k] (I : Ideal (MvPolynomial (Fin q) k))
      (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin q) k)),
      IsMonomial k q I → (∀ n,quotientHilbert k q I hI n=H n) →
      ∀ a,MinimalGenerator k q I a → a.degree≤B := by
  let T := (hilbertProfiles_finite q H).toFinset
  refine ⟨T.sup (fun p => (profileGenerators q p).sup Finsupp.degree),?_⟩
  intro k _ I hI hmono hH a ha
  have hp : monomialIdealProfile k q I∈T := by
    rw [Set.Finite.mem_toFinset]
    exact ⟨monomialIdealProfile_upper k q I,fun n =>
      (monomialIdealProfile_hilbert k q I hI hmono n).trans (hH n)⟩
  have ham : a∈profileGenerators q (monomialIdealProfile k q I) := by
    rw [profileGenerators,Set.Finite.mem_toFinset]
    simpa only [Set.mem_ofPred_eq,profileMinimal,monomialIdealProfile,decide_eq_true_eq,MinimalGenerator] using ha
  exact (Finset.le_sup (f:=Finsupp.degree) ham).trans (Finset.le_sup (f:=fun p => (profileGenerators q p).sup Finsupp.degree) hp)
end NSP14.Lex
