module
public import NSP14.Width.EdgeHoleMinor
public import NSP14.Width.EdgeHoleCounting
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open scoped Classical
open NSP14.Homological
namespace NSP14.Width
variable {σ : Type} [Fintype σ]

theorem missingWedge_card (B : Finset σ) (j : ℕ) :
    Fintype.card {F : KoszulWedge σ j // ¬B⊆F.val}+
      containingBlock B.card (Fintype.card σ-B.card) j=(Fintype.card σ).choose j := by
  let e : {F : KoszulWedge σ j // ¬B⊆F.val} ≃
      ↥(((Finset.univ : Finset σ).powersetCard j).filter (fun F => ¬B⊆F)) := {
    toFun a := ⟨a.val.val,Finset.mem_filter.mpr ⟨Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _,a.val.property⟩,a.property⟩⟩
    invFun a := ⟨⟨a.val,(Finset.mem_powersetCard.mp (Finset.mem_filter.mp a.property).1).2⟩,(Finset.mem_filter.mp a.property).2⟩
    left_inv _ := rfl
    right_inv _ := rfl }
  rw [Fintype.card_congr e,Fintype.card_coe]
  have hp := Finset.card_filter_add_card_filter_not (s:=(Finset.univ : Finset σ).powersetCard j) (fun F => B⊆F)
  have hb : (((Finset.univ : Finset σ).powersetCard j).filter (B⊆·)).card=
      containingBlock B.card (Fintype.card σ-B.card) j := by
    unfold containingBlock
    split_ifs with hj
    · simpa only [Finset.card_univ] using Finset.card_filter_powersetCard_subset B Finset.univ j (Finset.subset_univ _) hj
    · rw [Finset.card_eq_zero]
      apply Finset.filter_eq_empty_iff.mpr
      intro F hF hBF
      have hcard := Finset.card_le_card hBF
      have hFcard := (Finset.mem_powersetCard.mp hF).2
      omega
  rw [hb,Finset.card_powersetCard,Finset.card_univ] at hp
  omega

theorem containingBlock_pascal (r s i : ℕ) (hi : 1  ≤  i) :
    containingBlock r s (i-1)+containingBlock r s i=
      if r ≤ i then (s+1).choose (i-r) else 0 := by
  unfold containingBlock
  rcases lt_trichotomy r i with hr|hr|hr
  · rw [ite_eq_left (by omega),ite_eq_left (by omega),ite_eq_left (by omega),
      Nat.choose_succ_left s (i-r) (by omega)]
    rw [show i-1-r=i-r-1 by omega]
  · subst r
    simp [show ¬i  ≤  i-1 by omega]
  · rw [ite_eq_right (by omega),ite_eq_right (by omega),ite_eq_right (by omega)]
end NSP14.Width
namespace NSP14.Endpoint.Data.OneHole
variable {D : NSP14.Endpoint.Data} (H : D.OneHole)

noncomputable def minorIndexEquiv (j : ℕ) : H.MinorIndex j ≃
    ({F : KoszulWedge D.a j // ¬H.block false⊆F.val} ⊕
      {F : KoszulWedge D.a j // ¬H.block true⊆F.val}) where
  toFun a := if he : a.val.1=false then
      Sum.inl ⟨a.val.2,by simpa only [he] using a.property⟩
    else Sum.inr ⟨a.val.2,by
      have he' : a.val.1=true := by cases hb : a.val.1 <;> simp_all
      simpa only [he'] using a.property⟩
  invFun a := match a with
    | Sum.inl a => ⟨(false,a.val),a.property⟩
    | Sum.inr a => ⟨(true,a.val),a.property⟩
  left_inv := by
    rintro ⟨⟨p,F⟩,hp⟩
    cases p <;> rfl
  right_inv := by intro a; cases a <;> rfl

theorem block_partition : (H.block false).card+(H.block true).card=D.q := by
  have he : H.block false∪H.block true=Finset.univ := by
    ext b
    simp only [block,Finset.mem_union,Finset.mem_filter,Finset.mem_univ,true_and]
    cases H.side b <;> simp
  have hd : Disjoint (H.block false) (H.block true) := by
    apply Finset.disjoint_left.mpr
    intro b hb hc
    have hb' := (Finset.mem_filter.mp hb).2
    have hc' := (Finset.mem_filter.mp hc).2
    simp_all
  rw [←Finset.card_union_of_disjoint hd,he,Finset.card_univ,Fintype.card_coe]
  rfl

theorem minor_card (j : ℕ) :
    Fintype.card (H.MinorIndex j)+
      NSP14.Width.containingBlock (H.block false).card (H.block true).card j+
      NSP14.Width.containingBlock (H.block true).card (H.block false).card j=2*D.q.choose j := by
  have h0 := NSP14.Width.missingWedge_card (H.block false) j
  have h1 := NSP14.Width.missingWedge_card (H.block true) j
  rw [Fintype.card_congr (H.minorIndexEquiv j),Fintype.card_sum]
  rw [Fintype.card_coe] at h0 h1
  change _+NSP14.Width.containingBlock _ (D.q-_) j=D.q.choose j at h0 h1
  have hp := H.block_partition
  have hs0 : D.q-(H.block false).card=(H.block true).card := by omega
  have hs1 : D.q-(H.block true).card=(H.block false).card := by omega
  rw [hs0] at h0
  rw [hs1] at h1
  simp only [←Nat.card_eq_fintype_card] at h0 h1 ⊢
  dsimp only [KoszulWedge] at h0 h1 ⊢
  omega

theorem minor_card_pair (i : ℕ) (hi : 1  ≤  i) :
    Fintype.card (H.MinorIndex (i-1))+Fintype.card (H.MinorIndex i)+
      NSP14.Width.edgeCorrection (H.block false).card (H.block true).card i=
        2*(D.q.choose (i-1)+D.q.choose i) := by
  have h0 := H.minor_card (i-1)
  have h1 := H.minor_card i
  have hp0 := NSP14.Width.containingBlock_pascal (H.block false).card (H.block true).card i hi
  have hp1 := NSP14.Width.containingBlock_pascal (H.block true).card (H.block false).card i hi
  unfold NSP14.Width.edgeCorrection
  omega
end NSP14.Endpoint.Data.OneHole
