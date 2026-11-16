module
public import NSP14.Lex.BettiComparison
public import Mathlib.Algebra.MvPolynomial.Rename
@[expose] public section
open scoped Classical BigOperators
open NSP14.Homological
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace NSP14.Lex

def suffixExponent (s r : ℕ) (α : Fin r →₀ ℕ) : Fin (s+r) →₀ ℕ := α.embDomain (Fin.natAddEmb s)
@[simp] theorem suffixExponent_natAdd (s r : ℕ) (α : Fin r →₀ ℕ) (i : Fin r) :
    suffixExponent s r α (Fin.natAdd s i)=α i := Finsupp.embDomain_apply_self (Fin.natAddEmb s) α i

theorem suffixExponent_before (s r : ℕ) (α : Fin r →₀ ℕ) (i : Fin (s+r)) (hi : i.val<s) :
    suffixExponent s r α i=0 := by
  apply Finsupp.embDomain_of_notMem_range
  rintro ⟨j,hj⟩
  have he := congrArg Fin.val hj
  change s+j.val=i.val at he
  omega

@[simp] theorem suffixExponent_degree (s r : ℕ) (α : Fin r →₀ ℕ) :
    (suffixExponent s r α).degree=α.degree := by
  rw [suffixExponent,Finsupp.embDomain_eq_mapDomain,Finsupp.degree_mapDomain]

theorem suffixExponent_injective (s r : ℕ) : Function.Injective (suffixExponent s r) := by
  intro α β he
  ext i
  simpa only [suffixExponent_natAdd] using congrArg (fun γ => γ (Fin.natAdd s i)) he

theorem suffixExponent_lex_lt (s r : ℕ) (α β : Fin r →₀ ℕ)
    (h : MonomialOrder.lex.toSyn α<MonomialOrder.lex.toSyn β) :
    MonomialOrder.lex.toSyn (suffixExponent s r α)<MonomialOrder.lex.toSyn (suffixExponent s r β) := by
  change Finsupp.Lex (· < ·) (· < ·) α β at h
  change Finsupp.Lex (· < ·) (· < ·) (suffixExponent s r α) (suffixExponent s r β)
  obtain ⟨i,hi,hlt⟩ := h
  refine ⟨Fin.natAdd s i,?_,?_⟩
  · intro j hji
    by_cases hj : j.val<s
    · rw [suffixExponent_before s r α j hj,suffixExponent_before s r β j hj]
    · let j' : Fin r := ⟨j.val-s,by have:=j.isLt; omega⟩
      have he : Fin.natAdd s j'=j := Fin.ext (by dsimp [j']; omega)
      rw [← he,suffixExponent_natAdd,suffixExponent_natAdd]
      apply hi
      change j.val-s< i.val
      change j.val<s+i.val at hji
      omega
  · simpa only [suffixExponent_natAdd] using hlt

theorem suffixExponent_lex_le (s r : ℕ) (α β : Fin r →₀ ℕ)
    (h : MonomialOrder.lex.toSyn α≤MonomialOrder.lex.toSyn β) :
    MonomialOrder.lex.toSyn (suffixExponent s r α)≤MonomialOrder.lex.toSyn (suffixExponent s r β) := by
  rcases h.eq_or_lt with he|hlt
  · have hab : α=β := MonomialOrder.lex.toSyn.injective he
    subst β
    exact le_rfl
  · exact (suffixExponent_lex_lt s r α β hlt).le

def suffixHead (s r : ℕ) (α : Fin (s+r) →₀ ℕ) : Fin r →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun j => α (Fin.natAdd s j))
@[simp] theorem suffixHead_apply (s r : ℕ) (α : Fin (s+r) →₀ ℕ) (j : Fin r) :
    suffixHead s r α j=α (Fin.natAdd s j) := rfl
@[simp] theorem suffixHead_suffix (s r : ℕ) (α : Fin r →₀ ℕ) : suffixHead s r (suffixExponent s r α)=α := by
  ext j
  simp only [suffixHead_apply,suffixExponent_natAdd]

theorem suffixExponent_head (s r : ℕ) (α : Fin (s+r) →₀ ℕ) (ha : ∀ j,j.val<s → α j=0) :
    suffixExponent s r (suffixHead s r α)=α := by
  ext j
  by_cases hj : j.val<s
  · rw [suffixExponent_before s r _ j hj,ha j hj]
  · let j' : Fin r := ⟨j.val-s,by have:=j.isLt; omega⟩
    have he : Fin.natAdd s j'=j := Fin.ext (by dsimp [j']; omega)
    rw [← he,suffixExponent_natAdd,suffixHead_apply]

theorem suffixHead_degree (s r : ℕ) (α : Fin (s+r) →₀ ℕ) (ha : ∀ j,j.val<s → α j=0) :
    (suffixHead s r α).degree=α.degree := by
  have hh := congrArg Finsupp.degree (suffixExponent_head s r α ha)
  simpa only [suffixExponent_degree] using hh

theorem suffixExponent_maxVariable (s r : ℕ) (α : Fin r →₀ ℕ) (hn : α≠0) :
    maxVariable (s+r) (suffixExponent s r α)=s+maxVariable r α := by
  obtain ⟨j,hj,hm,hmax⟩ := maxVariable_spec r α hn
  rw [hm]
  apply le_antisymm
  · apply Finset.sup_le
    intro i hi
    have hpos := Finsupp.mem_support_iff.mp hi
    have hs : s≤ i.val := by
      by_contra hnot
      exact hpos (suffixExponent_before s r α i (by omega))
    let i' : Fin r := ⟨i.val-s,by have:=i.isLt; omega⟩
    have he : Fin.natAdd s i'=i := Fin.ext (by dsimp [i']; omega)
    have hi' : α i'≠0 := by simpa only [← he,suffixExponent_natAdd] using hpos
    have hij : i'≤j := by by_contra hnot; exact hi' (hmax i' (lt_of_not_ge hnot))
    change i.val+1≤s+(j.val+1)
    change i.val-s≤j.val at hij
    omega
  · have hi : Fin.natAdd s j∈(suffixExponent s r α).support := by
      apply Finsupp.mem_support_iff.mpr
      rw [suffixExponent_natAdd]
      omega
    simpa only [Fin.val_natAdd,Nat.add_assoc,maxVariable] using Finset.le_sup (f:=fun i : Fin (s+r) => i.val+1) hi

variable (k : Type) [Field k] (s r : ℕ)
attribute [local instance] MvPolynomial.gradedAlgebra

def suffixVariableIdeal (I : Ideal (MvPolynomial (Fin (s+r)) k)) : Ideal (MvPolynomial (Fin r) k) :=
  I.comap (MvPolynomial.rename (R:=k) (Fin.natAdd s : Fin r → Fin (s+r))).toRingHom

theorem suffixVariableIdeal_monomial (I : Ideal (MvPolynomial (Fin (s+r)) k)) (α : Fin r →₀ ℕ) :
    MvPolynomial.monomial α (1:k)∈suffixVariableIdeal k s r I ↔
      MvPolynomial.monomial (suffixExponent s r α) (1:k)∈I := by
  change MvPolynomial.rename (Fin.natAdd s) (MvPolynomial.monomial α (1:k))∈I ↔ _
  rw [MvPolynomial.rename_monomial,suffixExponent,Finsupp.embDomain_eq_mapDomain, ]
  rfl

theorem suffixVariableIdeal_isMonomial (I : Ideal (MvPolynomial (Fin (s+r)) k))
    (hI : IsMonomial k (s+r) I) : IsMonomial k r (suffixVariableIdeal k s r I) := by
  intro f hf α hα
  change MvPolynomial.rename (Fin.natAdd s) f∈I at hf
  have hs : suffixExponent s r α∈(MvPolynomial.rename (R:=k) (Fin.natAdd s) f).support := by
    rw [MvPolynomial.support_rename_of_injective (Fin.natAdd_injective r s)]
    exact Finset.mem_image.mpr ⟨α,hα,(Finsupp.embDomain_eq_mapDomain (Fin.natAddEmb s) α).symm⟩
  exact (suffixVariableIdeal_monomial k s r I α).mpr (hI _ hf _ hs)

theorem suffixVariableIdeal_isLex (I : Ideal (MvPolynomial (Fin (s+r)) k)) (hI : IsLex k (s+r) I) :
    IsLex k r (suffixVariableIdeal k s r I) := by
  refine ⟨suffixVariableIdeal_isMonomial k s r I hI.1,?_⟩
  intro α β hdeg hle hm
  rw [suffixVariableIdeal_monomial] at hm ⊢
  exact hI.2 _ _ (by simpa only [suffixExponent_degree] using hdeg) (suffixExponent_lex_le s r α β hle) hm


end NSP14.Lex
