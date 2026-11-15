module
public import Mathlib.Combinatorics.SetFamily.KruskalKatona
public import Mathlib.Data.Finset.Preimage
@[expose] public section
open scoped Classical BigOperators FinsetFamily
open Finset
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace NSP14.Lex
variable {n : ℕ}

def familyLift (A : Finset (Fin n)) : Finset (Fin (n+1)) := A.image Fin.succ

def familyDrop (A : Finset (Fin (n+1))) : Finset (Fin n) := A.preimage Fin.succ (Fin.succ_injective n).injOn

@[simp] theorem mem_familyLift (A : Finset (Fin n)) (x : Fin n) : x.succ∈familyLift A ↔ x∈A := by
  simp [familyLift]

@[simp] theorem zero_not_mem_familyLift (A : Finset (Fin n)) : (0 : Fin (n+1))∉familyLift A := by
  simp [familyLift]

@[simp] theorem familyDrop_familyLift (A : Finset (Fin n)) : familyDrop (familyLift A)=A := by
  ext x
  simp [familyDrop]

theorem familyLift_injective : Function.Injective (@familyLift n) := by
  intro A B he
  have hh := congrArg familyDrop he
  simpa only [familyDrop_familyLift] using hh

@[simp] theorem familyLift_card (A : Finset (Fin n)) : (familyLift A).card=A.card :=
  Finset.card_image_of_injective _ (Fin.succ_injective n)

theorem familyLift_familyDrop (A : Finset (Fin (n+1))) : familyLift (familyDrop A)=A.erase 0 := by
  ext x
  refine Fin.cases ?_ (fun y => ?_) x
  · simp
  · simp [familyDrop]

def zeroFreeFamily (F : Finset (Finset (Fin (n+1)))) : Finset (Finset (Fin n)) :=
  Finset.univ.filter (fun A => familyLift A∈F)

def zeroLinkFamily (F : Finset (Finset (Fin (n+1)))) : Finset (Finset (Fin n)) :=
  Finset.univ.filter (fun A => insert 0 (familyLift A)∈F)

@[simp] theorem mem_zeroFreeFamily (F : Finset (Finset (Fin (n+1)))) (A : Finset (Fin n)) :
    A∈zeroFreeFamily F ↔ familyLift A∈F := by simp [zeroFreeFamily]

@[simp] theorem mem_zeroLinkFamily (F : Finset (Finset (Fin (n+1)))) (A : Finset (Fin n)) :
    A∈zeroLinkFamily F ↔ insert 0 (familyLift A)∈F := by simp [zeroLinkFamily]

theorem zeroFreeFamily_card (F : Finset (Finset (Fin (n+1)))) :
    (zeroFreeFamily F).card=(F.filter (fun A => (0 : Fin (n+1))∉A)).card := by
  apply Finset.card_nbij familyLift
  · intro A hA
    exact Finset.mem_filter.mpr ⟨mem_zeroFreeFamily F A |>.mp hA,zero_not_mem_familyLift A⟩
  · exact familyLift_injective.injOn
  · intro A hA
    obtain ⟨hAF,hA0⟩ := Finset.mem_filter.mp hA
    refine ⟨familyDrop A,?_,?_⟩
    · change familyDrop A∈zeroFreeFamily F
      rw [mem_zeroFreeFamily,familyLift_familyDrop,Finset.erase_eq_of_notMem hA0]
      exact hAF
    · rw [familyLift_familyDrop,Finset.erase_eq_of_notMem hA0]

theorem zeroLinkFamily_card (F : Finset (Finset (Fin (n+1)))) :
    (zeroLinkFamily F).card=(F.filter (fun A => (0 : Fin (n+1))∈A)).card := by
  apply Finset.card_nbij (fun A => insert 0 (familyLift A))
  · intro A hA
    exact Finset.mem_filter.mpr ⟨mem_zeroLinkFamily F A |>.mp hA,Finset.mem_insert_self _ _⟩
  · intro A _ B _ he
    apply familyLift_injective
    have hh := congrArg (fun S : Finset (Fin (n+1)) => S.erase 0) he
    simpa only [Finset.erase_insert (zero_not_mem_familyLift A),Finset.erase_insert (zero_not_mem_familyLift B)] using hh
  · intro A hA
    obtain ⟨hAF,hA0⟩ := Finset.mem_filter.mp hA
    refine ⟨familyDrop A,?_,?_⟩
    · change familyDrop A∈zeroLinkFamily F
      rw [mem_zeroLinkFamily,familyLift_familyDrop,Finset.insert_erase hA0]
      exact hAF
    · change insert 0 (familyLift (familyDrop A))=A
      rw [familyLift_familyDrop,Finset.insert_erase hA0]

theorem zeroFamily_card_decomposition (F : Finset (Finset (Fin (n+1)))) :
    (zeroFreeFamily F).card+(zeroLinkFamily F).card=F.card := by
  rw [zeroFreeFamily_card,zeroLinkFamily_card,add_comm]
  exact Finset.card_filter_add_card_filter_not (s:=F) (p:=fun A => (0 : Fin (n+1))∈A)

theorem zeroFreeFamily_shadow_subset (F : Finset (Finset (Fin (n+1))))
    (hshift : ∀ A∈F,(0 : Fin (n+1))∉A → ∀ x∈A,insert 0 (A.erase x)∈F) :
    ∂ (zeroFreeFamily F)⊆zeroLinkFamily F := by
  intro A hA
  obtain ⟨B,hB,x,hx,rfl⟩ := Finset.mem_shadow_iff.mp hA
  rw [mem_zeroLinkFamily]
  have hh := hshift (familyLift B) (mem_zeroFreeFamily F B |>.mp hB) (zero_not_mem_familyLift B)
    x.succ ((mem_familyLift B x).mpr hx)
  simpa only [familyLift,Finset.image_erase (Fin.succ_injective n)] using hh
end NSP14.Lex

namespace NSP14.Lex
variable {n r : ℕ}

theorem zeroFreeFamily_sized (F : Finset (Finset (Fin (n+1))))
    (hF : (F : Set (Finset (Fin (n+1)))).Sized r) :
    (zeroFreeFamily F : Set (Finset (Fin n))).Sized r := by
  intro A hA
  have hh := hF ((mem_zeroFreeFamily F A).mp hA)
  simpa only [familyLift_card] using hh

theorem zeroLinkFamily_sized (F : Finset (Finset (Fin (n+1))))
    (hF : (F : Set (Finset (Fin (n+1)))).Sized r) :
    (zeroLinkFamily F : Set (Finset (Fin n))).Sized (r-1) := by
  intro A hA
  have hh := hF ((mem_zeroLinkFamily F A).mp hA)
  rw [Finset.card_insert_of_notMem (zero_not_mem_familyLift A),familyLift_card] at hh
  omega

theorem zeroFreeFamily_initSeg (F : Finset (Finset (Fin (n+1))))
    (hF : Finset.Colex.IsInitSeg F r) : Finset.Colex.IsInitSeg (zeroFreeFamily F) r := by
  refine ⟨zeroFreeFamily_sized F hF.1,?_⟩
  intro A B hA hBA
  rw [mem_zeroFreeFamily]
  exact hF.2 ((mem_zeroFreeFamily F A).mp hA)
    ⟨(Finset.Colex.toColex_image_lt_toColex_image Fin.strictMono_succ).mpr hBA.1,
      (familyLift_card B).trans hBA.2⟩

theorem zeroLink_initSeg_subset_shadow (F : Finset (Finset (Fin (n+1))))
    (hF : Finset.Colex.IsInitSeg F r) (B : Finset (Fin n))
    (hB : B.card=r) (hBn : B.Nonempty) (hBF : B∉zeroFreeFamily F) :
    zeroLinkFamily F⊆∂ (Finset.Colex.initSeg B) := by
  intro T hT
  have hTF := (mem_zeroLinkFamily F T).mp hT
  have hBL : familyLift B∉F := by simpa only [mem_zeroFreeFamily] using hBF
  have hcardS : (insert 0 (familyLift T)).card=r := hF.1 hTF
  have hlt : toColex (insert 0 (familyLift T))<toColex (familyLift B) := by
    rcases lt_trichotomy (toColex (insert 0 (familyLift T))) (toColex (familyLift B)) with h|h|h
    · exact h
    · have he : insert 0 (familyLift T)=familyLift B := toColex_inj.mp h
      exact False.elim (hBL (he ▸ hTF))
    · exact False.elim (hBL (hF.2 hTF ⟨h,(familyLift_card B).trans hB⟩))
  have hle := Finset.Colex.erase_le_erase_min' hlt.le
    (by rw [hcardS,familyLift_card,hB]) (Finset.mem_insert_self 0 (familyLift T))
  have hmin : (familyLift B).min' (hBn.image Fin.succ)=(B.min' hBn).succ :=
    Finset.min'_image Fin.strictMono_succ.monotone B (hBn.image Fin.succ)
  rw [Finset.erase_insert (zero_not_mem_familyLift T),hmin] at hle
  change toColex (familyLift T)≤toColex ((B.image Fin.succ).erase (B.min' hBn).succ) at hle
  rw [← Finset.image_erase (Fin.succ_injective n)] at hle
  have hsmall : toColex T≤toColex (B.erase (B.min' hBn)) :=
    (Finset.Colex.toColex_image_le_toColex_image Fin.strictMono_succ).mp hle
  rw [Finset.Colex.shadow_initSeg hBn,Finset.Colex.mem_initSeg]
  refine ⟨?_,hsmall⟩
  rw [Finset.card_erase_of_mem (Finset.min'_mem B hBn),hB]
  exact (zeroLinkFamily_sized F hF.1 hT).symm
end NSP14.Lex

namespace NSP14.Lex
variable {n r : ℕ}

theorem colex_next_initSeg (A : Finset (Finset (Fin n))) (hA : Finset.Colex.IsInitSeg A r)
    (hex : ∃ B : Finset (Fin n),B.card=r ∧ B∉A) :
    ∃ B : Finset (Fin n),B.card=r ∧ B∉A ∧ Finset.Colex.initSeg B=insert B A := by
  let bad := Finset.univ.filter (fun B : Finset (Fin n) => B.card=r ∧ B∉A)
  let D := bad.image toColex
  have hD : D.Nonempty := by
    obtain ⟨B,hBr,hBA⟩ := hex
    exact ⟨toColex B,Finset.mem_image.mpr ⟨B,by simp only [bad,Finset.mem_filter,Finset.mem_univ,true_and]; exact ⟨hBr,hBA⟩,rfl⟩⟩
  obtain ⟨B,hB,he⟩ := Finset.mem_image.mp (Finset.min'_mem D hD)
  have hBr : B.card=r ∧ B∉A := by simpa only [bad,Finset.mem_filter,Finset.mem_univ,true_and] using hB
  have hmin (T : Finset (Fin n)) (hTr : T.card=r) (hTA : T∉A) : toColex B≤toColex T := by
    rw [he]
    exact Finset.min'_le D _ (Finset.mem_image.mpr ⟨T,by
      simp only [bad,Finset.mem_filter,Finset.mem_univ,true_and]
      exact ⟨hTr,hTA⟩,rfl⟩)
  refine ⟨B,hBr.1,hBr.2,?_⟩
  ext T
  rw [Finset.Colex.mem_initSeg,Finset.mem_insert]
  constructor
  · rintro ⟨hcard,hle⟩
    by_cases heq : T=B
    · exact Or.inl heq
    · right
      by_contra hTA
      have hle' := hmin T (hcard.symm.trans hBr.1) hTA
      exact heq (toColex_inj.mp (le_antisymm hle hle'))
  · rintro (rfl|hTA)
    · exact ⟨rfl,le_rfl⟩
    · refine ⟨hBr.1.trans (hA.1 hTA).symm,?_⟩
      by_contra hle
      exact hBr.2 (hA.2 hTA ⟨lt_of_not_ge hle,hBr.1⟩)

/-- For a family closed under replacing a positive vertex by zero, a colex initial
segment of the same size has no more members containing zero. -/
theorem colex_zeroLink_card_le (F L : Finset (Finset (Fin (n+1)))) (hr : 1≤r)
    (hF : (F : Set (Finset (Fin (n+1)))).Sized r) (hL : Finset.Colex.IsInitSeg L r)
    (hcard : L.card≤F.card)
    (hshift : ∀ A∈F,(0 : Fin (n+1))∉A → ∀ x∈A,insert 0 (A.erase x)∈F) :
    (zeroLinkFamily L).card≤(zeroLinkFamily F).card := by
  by_contra hn
  have hlt : (zeroLinkFamily F).card<(zeroLinkFamily L).card := lt_of_not_ge hn
  have hsumF := zeroFamily_card_decomposition F
  have hsumL := zeroFamily_card_decomposition L
  have hfree : (zeroFreeFamily L).card<(zeroFreeFamily F).card := by omega
  have hnotSub : ¬zeroFreeFamily F⊆zeroFreeFamily L := by
    intro hsub
    have hh := Finset.card_le_card hsub
    omega
  obtain ⟨B0,hB0,hB0L⟩ := Finset.not_subset.mp hnotSub
  obtain ⟨B,hBr,hBL,he⟩ := colex_next_initSeg (zeroFreeFamily L) (zeroFreeFamily_initSeg L hL)
    ⟨B0,zeroFreeFamily_sized F hF hB0,hB0L⟩
  have hBn : B.Nonempty := Finset.card_pos.mp (by omega)
  have hCcard : (Finset.Colex.initSeg B).card≤(zeroFreeFamily F).card := by
    rw [he,Finset.card_insert_of_notMem hBL]
    omega
  have hCinit : Finset.Colex.IsInitSeg (Finset.Colex.initSeg B) r := by
    simpa only [hBr] using (Finset.Colex.isInitSeg_initSeg (s:=B))
  have hKK := Finset.kruskal_katona (zeroFreeFamily_sized F hF) hCcard hCinit
  have hlink := Finset.card_le_card (zeroLink_initSeg_subset_shadow L hL B hBr hBn hBL)
  have hsource := Finset.card_le_card (zeroFreeFamily_shadow_subset F hshift)
  omega
end NSP14.Lex

namespace NSP14.Lex
variable {n r : ℕ}
theorem colex_zero_mem_card_le (F L : Finset (Finset (Fin (n+1)))) (hr : 1≤r)
    (hF : (F : Set (Finset (Fin (n+1)))).Sized r) (hL : Finset.Colex.IsInitSeg L r)
    (hcard : L.card≤F.card)
    (hshift : ∀ A∈F,(0 : Fin (n+1))∉A → ∀ x∈A,insert 0 (A.erase x)∈F) :
    (L.filter (fun A => (0 : Fin (n+1))∈A)).card≤(F.filter (fun A => (0 : Fin (n+1))∈A)).card := by
  simpa only [zeroLinkFamily_card] using colex_zeroLink_card_le F L hr hF hL hcard hshift
end NSP14.Lex
