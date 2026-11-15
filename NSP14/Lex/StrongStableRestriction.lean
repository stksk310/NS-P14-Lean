module
public import NSP14.Lex.DegreeFamily
public import NSP14.Lex.PrefixDominance
@[expose] public section
open scoped Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace NSP14.Lex

theorem orderEmbedding_zero_exchange {r N : ℕ} (e f : Fin r ↪o Fin (N+1)) (j : Fin r)
    (hzero : (0 : Fin (N+1))∉Finset.univ.image e)
    (himage : Finset.univ.image f=insert 0 ((Finset.univ.image e).erase (e j))) :
    ∀ i,f i≤e i := by
  let C := insert 0 ((Finset.univ.image e).erase (e j))
  let g (i : Fin r) : Fin (N+1) :=
    if i.val=0 then 0 else if i.val≤j.val then e ⟨i.val-1,by omega⟩ else e i
  have hpos (i : Fin r) : (0 : Fin (N+1))<e i := by
    have hne : e i≠0 := fun he => hzero (he ▸ Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩)
    change 0<(e i).val
    have hn : (e i).val≠0 := fun he => hne (Fin.ext he)
    omega
  have hg : StrictMono g := by
    intro i k hik
    have hikv : i.val<k.val := hik
    by_cases hi : i.val=0
    · have hk : k.val≠0 := by omega
      simp only [g,hi,ite_true,hk,ite_false]
      split_ifs
      · exact hpos _
      · exact hpos _
    · have hk : k.val≠0 := by omega
      simp only [g,hi,hk,ite_false]
      split_ifs with hij hkj hkj
      · apply e.strictMono
        change i.val-1<k.val-1
        omega
      · apply e.strictMono
        change i.val-1<k.val
        omega
      · omega
      · exact e.strictMono hik
  have hgc (i : Fin r) : g i∈C := by
    by_cases hi : i.val=0
    · simp only [g,hi,ite_true,C,Finset.mem_insert,true_or]
    · simp only [g,hi,ite_false]
      split_ifs with hij
      · apply Finset.mem_insert_of_mem
        apply Finset.mem_erase.mpr
        refine ⟨?_,Finset.mem_image.mpr ⟨⟨i.val-1,by omega⟩,Finset.mem_univ _,rfl⟩⟩
        intro he
        have hh := congrArg Fin.val (e.injective he)
        change i.val-1=j.val at hh
        omega
      · apply Finset.mem_insert_of_mem
        apply Finset.mem_erase.mpr
        refine ⟨?_,Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩⟩
        intro he
        have hh := congrArg Fin.val (e.injective he)
        omega
  change Finset.univ.image f=C at himage
  have hCcard : C.card=r := by
    rw [← himage,Finset.card_image_of_injective _ f.injective,Finset.card_univ,Fintype.card_fin]
  have hG := Finset.orderEmbOfFin_unique hCcard hgc hg
  have hF : (f : Fin r → Fin (N+1))=C.orderEmbOfFin hCcard :=
    Finset.orderEmbOfFin_unique hCcard (fun i => by
      rw [← himage]
      exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩) f.strictMono
  have hfg : (f : Fin r → Fin (N+1))=g := hF.trans hG.symm
  intro i
  rw [congrFun hfg i]
  by_cases hi : i.val=0
  · simp only [g,hi,ite_true]
    exact Fin.zero_le _
  · simp only [g,hi,ite_false]
    split_ifs
    · apply e.monotone
      change i.val-1 ≤ i.val
      omega
    · exact le_rfl
end NSP14.Lex

namespace NSP14.Lex

theorem separatorEmbedding_tail_le (q d : ℕ) (α β : PolynomialDegreeIndex (q+1) d)
    (hsep : ∀ i,degreeSeparatorEmbedding q d β i≤degreeSeparatorEmbedding q d α i) :
    ∀ t,t≤q+1 → reversedPrefix q β.val t≤reversedPrefix q α.val t := by
  intro t ht
  by_cases ht0 : t=0
  · subst t
    exact le_rfl
  by_cases htl : t=q+1
  · rw [htl,reversedPrefix_total,reversedPrefix_total,α.property,β.property]
  let i : Fin q := ⟨t-1,by omega⟩
  have hh := hsep i
  change i.val+reversedPrefix q β.val (i.val+1) ≤ i.val+reversedPrefix q α.val (i.val+1) at hh
  have hit : i.val+1=t := by dsimp only [i]; omega
  rw [hit] at hh
  omega

variable (k : Type) [Field k] (q d : ℕ)

theorem degreeIdealFamily_zero_shift (I : Ideal (MvPolynomial (Fin (q+2)) k))
    (hI : IsStronglyStable k (q+2) I) :
    ∀ B∈degreeIdealFamily k (q+1) d I,(0 : Fin (d+q+1))∉B →
      ∀ x∈B,insert 0 (B.erase x)∈degreeIdealFamily k (q+1) d I := by
  intro B hB hz x hx
  obtain ⟨α,hα,rfl⟩ := Finset.mem_image.mp hB
  simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hα
  obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hx
  let C := insert 0 ((degreeSeparator (q+1) d α).erase (degreeSeparatorEmbedding (q+1) d α j))
  have hjmem : degreeSeparatorEmbedding (q+1) d α j∈degreeSeparator (q+1) d α :=
    Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩
  have hCcard : C.card=q+1 := by
    dsimp only [C]
    rw [Finset.card_insert_of_notMem (fun h => hz (Finset.mem_of_mem_erase h)),
      Finset.card_erase_of_mem hjmem,degreeSeparator_card]
    omega
  let β := (degreeSeparatorEquiv (q+1) d).symm ⟨C,hCcard⟩
  have hβ : degreeSeparator (q+1) d β=C := by
    exact congrArg Subtype.val ((degreeSeparatorEquiv (q+1) d).apply_symm_apply ⟨C,hCcard⟩)
  have hsep : ∀ i,degreeSeparatorEmbedding (q+1) d β i≤degreeSeparatorEmbedding (q+1) d α i :=
    orderEmbedding_zero_exchange (degreeSeparatorEmbedding (q+1) d α)
      (degreeSeparatorEmbedding (q+1) d β) j hz hβ
  have hdom := separatorEmbedding_tail_le (q+1) d α β hsep
  have hmem : MvPolynomial.monomial β.val (1:k)∈I :=
    hI.mem_of_tail_le k (q+1) I α.val β.val (α.property.trans β.property.symm) hdom hα
  apply Finset.mem_image.mpr
  exact ⟨β,by simp only [Finset.mem_filter,Finset.mem_univ,true_and]; exact hmem,hβ⟩

/-- A proved cardinal restriction of actual strongly stable and lex monomial sets. -/
theorem IsStronglyStable.last_zero_count_le
    (I L : Ideal (MvPolynomial (Fin (q+2)) k)) (hI : IsStronglyStable k (q+2) I)
    (hL : IsLex k (q+2) L)
    (hcard : Fintype.card {α : PolynomialDegreeIndex (q+2) d // MvPolynomial.monomial α.val (1:k)∈L}≤
      Fintype.card {α : PolynomialDegreeIndex (q+2) d // MvPolynomial.monomial α.val (1:k)∈I}) :
    (Finset.univ.filter (fun α : PolynomialDegreeIndex (q+2) d =>
      MvPolynomial.monomial α.val (1:k)∈L ∧ α.val (Fin.last (q+1))=0)).card≤
    (Finset.univ.filter (fun α : PolynomialDegreeIndex (q+2) d =>
      MvPolynomial.monomial α.val (1:k)∈I ∧ α.val (Fin.last (q+1))=0)).card := by
  have hfc : (degreeIdealFamily k (q+1) d L).card≤(degreeIdealFamily k (q+1) d I).card := by
    simpa only [degreeIdealFamily_card] using hcard
  have hh := colex_zeroLink_card_le (degreeIdealFamily k (q+1) d I) (degreeIdealFamily k (q+1) d L)
    (by omega) (degreeIdealFamily_sized k (q+1) d I) (degreeIdealFamily_isInitSeg k (q+1) d L hL)
    hfc (degreeIdealFamily_zero_shift k q d I hI)
  simpa only [degreeIdealFamily_zeroLink_card] using hh
end NSP14.Lex
