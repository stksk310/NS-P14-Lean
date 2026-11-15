module
public import NSP14.Lex.GenericDistractionStable
public import NSP14.Lex.PrefixOrder
public import NSP14.Lex.Uniqueness
public import Mathlib.Order.Preorder.Finite
@[expose] public section
open scoped Classical BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] MvPolynomial.gradedAlgebra
namespace NSP14.Lex

structure GenericFieldStage where
  carrier : Type
  instField : Field carrier
attribute [instance] GenericFieldStage.instField

variable (k : Type) [Field k] (q : ℕ)

def genericFieldStage : ℕ → GenericFieldStage
  | 0 => ⟨k,inferInstance⟩
  | n+1 => ⟨GenericDistractionField (genericFieldStage n).carrier q,inferInstance⟩

abbrev genericTowerField (n : ℕ) := (genericFieldStage k q n).carrier

instance genericTowerField_field (n : ℕ) : Field (genericTowerField k q n) :=
  (genericFieldStage k q n).instField

def genericTowerMap : (n : ℕ) → k →+* genericTowerField k q n
  | 0 => RingHom.id k
  | n+1 => (algebraMap (genericTowerField k q n)
      (GenericDistractionField (genericTowerField k q n) q)).comp (genericTowerMap n)

def genericIdealTower (I : Ideal (MvPolynomial (Fin q) k)) :
    (n : ℕ) → Ideal (MvPolynomial (Fin q) (genericTowerField k q n))
  | 0 => initialIdeal k q MonomialOrder.degLex I
  | n+1 => genericMonomialStep (genericTowerField k q n) q (genericIdealTower I n)

theorem genericIdealTower_homogeneous (I : Ideal (MvPolynomial (Fin q) k)) (n : ℕ) :
    (genericIdealTower k q I n).IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin q) (genericTowerField k q n)) := by
  cases n with
  | zero => exact initialIdeal_homogeneous k q MonomialOrder.degLex I
  | succ n => exact genericMonomialStep_homogeneous (genericTowerField k q n) q _

theorem genericIdealTower_isMonomial (I : Ideal (MvPolynomial (Fin q) k)) (n : ℕ) :
    IsMonomial (genericTowerField k q n) q (genericIdealTower k q I n) := by
  cases n with
  | zero => exact initialIdeal_isMonomial k q MonomialOrder.degLex I
  | succ n => exact genericMonomialStep_isMonomial (genericTowerField k q n) q _

theorem genericIdealTower_sameHilbert (I : Ideal (MvPolynomial (Fin q) k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin q) k))
    (n d : ℕ) : quotientHilbert k q I hI d=
    quotientHilbert (genericTowerField k q n) q (genericIdealTower k q I n)
      (genericIdealTower_homogeneous k q I n) d := by
  induction n with
  | zero => exact initialIdeal_sameHilbert k q I hI d
  | succ n hn => exact hn.trans (genericMonomialStep_sameHilbert (genericTowerField k q n) q _
      (genericIdealTower_homogeneous k q I n) (genericIdealTower_isMonomial k q I n) d)

theorem genericIdealTower_gradedBetti_le (I : Ideal (MvPolynomial (Fin q) k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin q) k))
    (n i : ℕ) (t : ℤ) : quotientGradedBetti k q I hI i t≤
    quotientGradedBetti (genericTowerField k q n) q (genericIdealTower k q I n)
      (genericIdealTower_homogeneous k q I n) i t := by
  induction n with
  | zero => exact quotientGradedBetti_initial_le k q I hI i t
  | succ n hn => exact hn.trans (genericMonomialStep_gradedBetti_le (genericTowerField k q n) q _
      (genericIdealTower_homogeneous k q I n) (genericIdealTower_isMonomial k q I n) i t)

theorem genericIdealTower_profile_range_finite (I : Ideal (MvPolynomial (Fin q) k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin q) k)) :
    (Set.range (fun n => monomialIdealProfile (genericTowerField k q n) q
      (genericIdealTower k q I n))).Finite := by
  apply (hilbertProfiles_finite q (quotientHilbert k q I hI)).subset
  rintro p ⟨n,rfl⟩
  refine ⟨monomialIdealProfile_upper _ _ _,?_⟩
  intro d
  exact (monomialIdealProfile_hilbert _ _ _ (genericIdealTower_homogeneous k q I n)
    (genericIdealTower_isMonomial k q I n) d).trans (genericIdealTower_sameHilbert k q I hI n d).symm

/-- The actual comparison follows at any lex stage. Existence of such a stage is not assumed proved. -/
theorem genericIdealTower_lex_comparison (I L : Ideal (MvPolynomial (Fin q) k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin q) k))
    (hL : L.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin q) k))
    (hlL : IsLex k q L) (hH : ∀ d,quotientHilbert k q I hI d=quotientHilbert k q L hL d)
    (n : ℕ) (hlex : IsLex (genericTowerField k q n) q (genericIdealTower k q I n))
    (i : ℕ) (t : ℤ) : quotientGradedBetti k q I hI i t≤quotientGradedBetti k q L hL i t := by
  let F := genericTowerField k q n
  let : Algebra k F := (genericTowerMap k q n).toAlgebra
  have he : genericIdealTower k q I n=monomialExtension k F q L :=
    IsLex.eq_of_sameHilbert F q _ _ (genericIdealTower_homogeneous k q I n)
      (monomialExtension_homogeneous k F q L) hlex (monomialExtension_isLex k F q L hlL)
      (fun d => (genericIdealTower_sameHilbert k q I hI n d).symm.trans
        ((hH d).trans (monomialExtension_sameHilbert k F q L hL hlL.1 d)))
  have hb := genericIdealTower_gradedBetti_le k q I hI n i t
  have hb' : quotientGradedBetti k q I hI i t≤
      quotientGradedBetti F q (monomialExtension k F q L)
        (monomialExtension_homogeneous k F q L) i t := by simpa only [he] using hb
  exact hb'.trans_eq (monomialExtension_gradedBetti k F q L hL hlL.1 i t)
end NSP14.Lex

namespace NSP14.Lex
variable (k : Type) [Field k] (q : ℕ)
attribute [local instance] MvPolynomial.gradedAlgebra

theorem monomialIdealProfile_prefixCard (I : Ideal (MvPolynomial (Fin q) k))
    (n : ℕ) (v : PolynomialDegreeIndex q n) :
    profilePrefixCard q (monomialIdealProfile k q I) n v=monomialPrefixCard k q I n v := by
  simp only [profilePrefixCard,monomialPrefixCard,MonomialPrefix,monomialIdealProfile,
    Fintype.card_subtype,decide_eq_true_eq]

theorem genericMonomialStep_profileDominates (I : Ideal (MvPolynomial (Fin q) k)) :
    ProfileDominates q (monomialIdealProfile k q I)
      (monomialIdealProfile (GenericDistractionField k q) q (genericMonomialStep k q I)) := by
  intro n v
  rw [monomialIdealProfile_prefixCard,monomialIdealProfile_prefixCard]
  exact genericMonomialStep_prefixCard_le k q I n v

/-- Actual iterated supports stabilize. Lexness of the stationary support is a separate assertion. -/
theorem genericIdealTower_profile_stabilizes (I : Ideal (MvPolynomial (Fin q) k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin q) k)) :
    ∃ N : ℕ,∀ n,N≤n →
      monomialIdealProfile (genericTowerField k q n) q (genericIdealTower k q I n)=
        monomialIdealProfile (genericTowerField k q N) q (genericIdealTower k q I N) := by
  let f := fun n => monomialIdealProfile (genericTowerField k q n) q (genericIdealTower k q I n)
  let : PartialOrder (MonomialProfile q) := profileDominanceOrder q
  let : Preorder (MonomialProfile q) := (profileDominanceOrder q).toPreorder
  let : LE (MonomialProfile q) := (profileDominanceOrder q).toLE
  let : LT (MonomialProfile q) := (profileDominanceOrder q).toLT
  have hm : Monotone f := monotone_nat_of_le_succ (fun n =>
    genericMonomialStep_profileDominates (genericTowerField k q n) q (genericIdealTower k q I n))
  have hr := genericIdealTower_profile_range_finite k q I hI
  obtain ⟨p,⟨N,rfl⟩,hmax⟩ := hr.exists_maximal ⟨f 0,⟨0,rfl⟩⟩
  refine ⟨N,fun n hn => ?_⟩
  exact le_antisymm (hmax ⟨n,rfl⟩ (hm hn)) (hm hn)
end NSP14.Lex

namespace NSP14.Lex
attribute [local instance] MvPolynomial.gradedAlgebra
variable (k : Type) [Field k] (q : ℕ)

theorem exists_stronglyStable_comparison (I : Ideal (MvPolynomial (Fin q) k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin q) k)) :
    ∃ (L : Type) (fieldL : Field L),
      letI : Field L := fieldL
      ∃ (_ : Algebra k L) (J : Ideal (MvPolynomial (Fin q) L))
        (hJ : J.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin q) L)),
        IsMonomial L q J ∧
        (∀ v,MvPolynomial.monomial v (1:L)∈J →
          ∀ a b,0<v b → a<b → MvPolynomial.monomial (raisedExponent q v a b) (1:L)∈J) ∧
        (∀ n,quotientHilbert k q I hI n=quotientHilbert L q J hJ n) ∧
        (∀ i t,quotientGradedBetti k q I hI i t≤quotientGradedBetti L q J hJ i t) := by
  obtain ⟨N,hN⟩ := genericIdealTower_profile_stabilizes k q I hI
  let F := genericTowerField k q N
  let J := genericIdealTower k q I N
  have hfix (v : Fin q →₀ ℕ) :
      MvPolynomial.monomial v (1:GenericDistractionField F q)∈genericMonomialStep F q J ↔
        MvPolynomial.monomial v (1:F)∈J := by
    have he := congrArg (fun p : MonomialProfile q => p v=true) (hN (N+1) (by omega))
    change (decide (MvPolynomial.monomial v (1:GenericDistractionField F q)∈genericMonomialStep F q J)=true)=
      (decide (MvPolynomial.monomial v (1:F)∈J)=true) at he
    simpa only [decide_eq_true_eq] using Iff.of_eq he
  have hstable := genericMonomialStep_fixed_stronglyStable F q J
    (genericIdealTower_isMonomial k q I N) hfix
  exact ⟨F,inferInstance,(genericTowerMap k q N).toAlgebra,J,genericIdealTower_homogeneous k q I N,
    hstable.1,hstable.2,genericIdealTower_sameHilbert k q I hI N,
    genericIdealTower_gradedBetti_le k q I hI N⟩
end NSP14.Lex
