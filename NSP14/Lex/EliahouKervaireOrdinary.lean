module
public import NSP14.Lex.EliahouKervaireStep
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open scoped Classical BigOperators
open NSP14.Homological
namespace NSP14.Lex
variable (k : Type) [Field k] (q : ℕ)

noncomputable def monomialListIdeal (vs : List (Fin q →₀ ℕ)) : Ideal (MvPolynomial (Fin q) k) :=
  Ideal.span ((fun v => MvPolynomial.monomial v (1:k)) '' {v | v ∈ vs})

theorem monomialListIdeal_nil : monomialListIdeal k q []=⊥ := by simp [monomialListIdeal]

theorem monomialListIdeal_append (vs ws : List (Fin q →₀ ℕ)) :
    monomialListIdeal k q (vs++ws)=monomialListIdeal k q vs ⊔ monomialListIdeal k q ws := by
  have hs : {v | v ∈ vs++ws}={v | v ∈ vs} ∪ {v | v ∈ ws} := by ext v; simp
  unfold monomialListIdeal
  rw [hs,Set.image_union,Ideal.span_union]

theorem monomialListIdeal_singleton (w : Fin q →₀ ℕ) :
    monomialListIdeal k q [w]=Ideal.span {MvPolynomial.monomial w (1:k)} := by
  simp [monomialListIdeal]

theorem generatorList_mem (L : Ideal (MvPolynomial (Fin q) k)) (v : Fin q →₀ ℕ) :
    v ∈ generatorList q k L ↔ MinimalGenerator k q L v := by
  rw [← List.mem_toFinset,generatorList_toFinset,mem_minimalGeneratorFinset]

theorem generatorListIdeal_eq (L : Ideal (MvPolynomial (Fin q) k)) (hL : IsMonomial k q L) :
    monomialListIdeal k q (generatorList q k L)=L := by
  have hs : {v | v ∈ generatorList q k L}={v | MinimalGenerator k q L v} := by
    ext v
    exact generatorList_mem k q L v
  unfold monomialListIdeal
  rw [hs]
  exact (hL.span_minimal k q).symm

theorem predecessorIdeal_of_split (L : Ideal (MvPolynomial (Fin q) k))
    (pre rest : List (Fin q →₀ ℕ)) (w : Fin q →₀ ℕ)
    (hsplit : generatorList q k L=pre++w::rest) :
    predecessorIdeal k q L w=monomialListIdeal k q pre := by
  have hp : (pre++w::rest).Pairwise (precedes q) := hsplit ▸ generatorList_pairwise q k L
  have hleft := (List.pairwise_append.mp hp).2.2
  have hright := (List.pairwise_cons.mp (List.pairwise_append.mp hp).2.1).1
  have hs : {v | MinimalGenerator k q L v ∧ precedes q v w}={v | v ∈ pre} := by
    ext v
    constructor
    · rintro ⟨hm,hv⟩
      have hf := (generatorList_mem k q L v).mpr hm
      rw [hsplit] at hf
      rcases List.mem_append.mp hf with hpre|hrest
      · exact hpre
      · rcases List.mem_cons.mp hrest with he|he
        · subst v
          exact False.elim (not_precedes_self q w hv)
        · exact False.elim (not_precedes_self q w (precedes_trans q (hright v he) hv))
    · intro hv
      refine ⟨?_,hleft v hv w List.mem_cons_self⟩
      apply (generatorList_mem k q L v).mp
      rw [hsplit]
      exact List.mem_append.mpr (Or.inl hv)
  rw [predecessorIdeal_minimal q k L w,hs]
  rfl

theorem monomialList_empty_betti (i : ℕ) :
    totalBetti k (Fin q)
      (ModuleCat.of (MvPolynomial (Fin q) k) ((MvPolynomial (Fin q) k) ⧸ monomialListIdeal k q [])) (i+1)=0 := by
  rw [monomialListIdeal_nil]
  let e := (Submodule.quotEquivOfEqBot (⊥ : Ideal (MvPolynomial (Fin q) k)) rfl).toModuleIso
  exact (totalBetti_iso k (Fin q) e (i+1)).trans (totalBetti_free_succ k (Fin q) i)

/-- Finite induction through the actual ordered generators. Each step
is the previously constructed actual colon sequence, not a resolution premise. -/
theorem IsLex.ordinary_ek_accum {L : Ideal (MvPolynomial (Fin q) k)}
    (hL : IsLex k q L) (hproper : L ≠ ⊤)
    (pre rest : List (Fin q →₀ ℕ)) (hsplit : generatorList q k L=pre++rest) (i : ℕ) :
    totalBetti k (Fin q) (ModuleCat.of (MvPolynomial (Fin q) k) ((MvPolynomial (Fin q) k) ⧸ L)) (i+1)=
      totalBetti k (Fin q)
        (ModuleCat.of (MvPolynomial (Fin q) k) ((MvPolynomial (Fin q) k) ⧸ monomialListIdeal k q pre)) (i+1)+
      (rest.map (fun v => (maxVariable q v-1).choose i)).sum := by
  induction rest generalizing pre with
  | nil =>
    have he : generatorList q k L=pre := by simpa only [List.append_nil] using hsplit
    have hp : monomialListIdeal k q pre=L := by
      rw [←he]
      exact generatorListIdeal_eq k q L hL.1
    rw [hp]
    simp
  | cons w rest ih =>
    have hm : MinimalGenerator k q L w := by
      apply (generatorList_mem k q L w).mp
      rw [hsplit]
      exact List.mem_append.mpr (Or.inr List.mem_cons_self)
    have hsplit' : generatorList q k L=(pre++[w])++rest := by
      simpa only [List.append_assoc,List.singleton_append] using hsplit
    have hh := ih (pre++[w]) hsplit'
    have hs := hL.predecessor_betti_binomial k q hproper w hm i
    dsimp only at hs
    rw [predecessorIdeal_of_split k q L pre rest w hsplit] at hs
    have hsnoc : monomialListIdeal k q (pre++[w])=
        monomialListIdeal k q pre ⊔ Ideal.span {MvPolynomial.monomial w (1:k)} := by
      rw [monomialListIdeal_append,monomialListIdeal_singleton]
    rw [←hsnoc] at hs
    rw [hs] at hh
    simpa only [List.map_cons,List.sum_cons,add_assoc] using hh

theorem list_sum_map_toFinset (vs : List (Fin q →₀ ℕ)) (hn : vs.Nodup) (f : (Fin q →₀ ℕ) → ℕ) :
    (vs.map f).sum=∑ v ∈ vs.toFinset,f v := by
  induction vs with
  | nil => simp
  | cons v vs ih =>
    have hnv : v ∉ vs := (List.nodup_cons.mp hn).1
    simp only [List.map_cons,List.sum_cons,List.toFinset_cons]
    rw [Finset.sum_insert (by simpa only [List.mem_toFinset] using hnv),ih (List.nodup_cons.mp hn).2]

/-- Ordinary quotient EK over arbitrary fields, for the actual finite
minimal generator set. The internal-degree formula is not asserted here. -/
theorem IsLex.ordinary_ek {L : Ideal (MvPolynomial (Fin q) k)}
    (hL : IsLex k q L) (hproper : L ≠ ⊤) (g : Finset (Fin q →₀ ℕ))
    (hg : ∀ v,v ∈ g ↔ MinimalGenerator k q L v) (i : ℕ) (hi : 1 ≤ i) :
    totalBetti k (Fin q) (ModuleCat.of (MvPolynomial (Fin q) k) ((MvPolynomial (Fin q) k) ⧸ L)) i=
      ∑ v ∈ g,(maxVariable q v-1).choose (i-1) := by
  obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0)
  have hh := hL.ordinary_ek_accum k q hproper [] (generatorList q k L) rfl j
  rw [monomialList_empty_betti,zero_add] at hh
  have hn : (generatorList q k L).Nodup := Finset.sort_nodup _ _
  rw [list_sum_map_toFinset q _ hn,generatorList_toFinset] at hh
  have he : minimalGeneratorFinset k q L=g := by
    ext v
    rw [mem_minimalGeneratorFinset,hg]
  rw [he] at hh
  simpa only [Nat.succ_eq_add_one,Nat.add_sub_cancel] using hh

end NSP14.Lex
