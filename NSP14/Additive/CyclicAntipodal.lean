module
public import NSP14.Additive.FourPointGrowth
@[expose] public section
open scoped Pointwise Classical
namespace NSP14.Additive
def CyclicAntipodal (u : ℕ) (A : Finset (ZMod u)) : Prop :=
  ∃ h t : ℕ, u=2*h ∧ 0 < t ∧ t < h ∧ Nat.Coprime t h ∧
    A = {0,(t : ZMod u),(h : ZMod u),((t+h : ℕ) : ZMod u)}

theorem generated_four_coprime {u h t : ℕ} (hu : u=2*h)
    (A : Finset (ZMod u))
    (he : A = {0,(t : ZMod u),(h : ZMod u),((t+h : ℕ) : ZMod u)})
    (hgen : AddSubgroup.closure (A : Set (ZMod u))=⊤) : Nat.Coprime t h := by
  let g := Nat.gcd t h
  have hgt : g ∣ t := Nat.gcd_dvd_left t h
  have hgh : g ∣ h := Nat.gcd_dvd_right t h
  have hgu : g ∣ u := by rw [hu]; exact dvd_mul_of_dvd_right hgh 2
  let f : ZMod u →+ ZMod g := (ZMod.castHom hgu (ZMod g)).toAddMonoidHom
  have hf (x : ZMod u) (hx : x ∈ A) : f x = 0 := by
    rw [he] at hx
    simp only [Finset.mem_insert,Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact f.map_zero
    · change (ZMod.castHom hgu (ZMod g)) (t : ZMod u)=0
      rw [map_natCast]
      exact (ZMod.natCast_eq_zero_iff _ _).mpr hgt
    · change (ZMod.castHom hgu (ZMod g)) (h : ZMod u)=0
      rw [map_natCast]
      exact (ZMod.natCast_eq_zero_iff _ _).mpr hgh
    · change (ZMod.castHom hgu (ZMod g)) ((t+h : ℕ) : ZMod u)=0
      rw [map_natCast]
      exact (ZMod.natCast_eq_zero_iff _ _).mpr (dvd_add hgt hgh)
  have hl : AddSubgroup.closure (A : Set (ZMod u)) ≤ f.ker :=
    (AddSubgroup.closure_le _).mpr hf
  rw [hgen] at hl
  have h1 := hl (show (1 : ZMod u) ∈ (⊤ : AddSubgroup (ZMod u)) from trivial)
  change (ZMod.castHom hgu (ZMod g)) 1=0 at h1
  rw [map_one] at h1
  have hd : g ∣ 1 := (ZMod.natCast_eq_zero_iff 1 g).mp (by simpa using h1)
  exact Nat.coprime_iff_gcd_eq_one.mpr (Nat.dvd_one.mp hd)

theorem twoCoset_antipodal {u : ℕ} [NeZero u] (A : Finset (ZMod u))
    (hgen : AddSubgroup.closure (A : Set (ZMod u))=⊤) (hex : TwoCosetException A) :
    CyclicAntipodal u A := by
  obtain ⟨H,hH,t₀,htH,hA⟩ := hex
  let F := (H : Set (ZMod u)).toFinset
  have h0 : (0 : ZMod u) ∈ F := by simp [F]
  have hcard : F.card=2 := by
    rw [show F.card = Fintype.card H from Set.toFinset_card _]
    simpa only [Nat.card_eq_fintype_card] using hH
  have hecard : (F.erase 0).card=1 := by
    have hh := Finset.card_erase_add_one h0
    omega
  obtain ⟨b,hb⟩ := Finset.card_eq_one.mp hecard
  have hbmem : b ∈ F.erase 0 := by rw [hb]; simp
  have hb0 : b ≠ 0 := (Finset.mem_erase.mp hbmem).1
  have hbH : b ∈ H := Set.mem_toFinset.mp (Finset.mem_erase.mp hbmem).2
  have hF : F={0,b} := by
    rw [←Finset.insert_erase h0,hb]
  have hbb : b+b=0 := by
    have hm : b+b ∈ F := Set.mem_toFinset.mpr (H.add_mem hbH hbH)
    rw [hF,Finset.mem_insert,Finset.mem_singleton] at hm
    rcases hm with he | he
    · exact he
    · exact False.elim (hb0 (add_left_cancel (he.trans (add_zero b).symm)))
  let h := b.val
  have hpos : 0 < h := ZMod.val_pos.mpr hb0
  have hd : u ∣ h+h := by
    apply (ZMod.natCast_eq_zero_iff _ _).mp
    change ((b.val+b.val : ℕ) : ZMod u)=0
    simpa only [Nat.cast_add,ZMod.natCast_zmod_val] using hbb
  have hlt : h < u := ZMod.val_lt b
  have hu : u=2*h := by
    obtain ⟨k,hk⟩ := hd
    have hku : k ≠ 0 := by intro he; rw [he,mul_zero] at hk; omega
    have hk2 : k < 2 := by
      by_contra hn
      have hh := Nat.mul_le_mul_left u (show 2 ≤ k by omega)
      nlinarith
    have hk1 : k=1 := by omega
    rw [hk1,mul_one] at hk
    omega
  have hbeq : b=(h : ZMod u) := (ZMod.natCast_zmod_val b).symm
  have ht0 : t₀ ≠ 0 := fun he => htH (he ▸ H.zero_mem)
  have htb : t₀ ≠ b := fun he => htH (he ▸ hbH)
  have htpos : 0 < t₀.val := ZMod.val_pos.mpr ht0
  have htlt : t₀.val < 2*h := by rw [←hu]; exact ZMod.val_lt _
  have htvne : t₀.val ≠ h := by
    intro he
    apply htb
    apply ZMod.val_injective u
    exact he
  have hA' : A = {0,b,t₀,t₀+b} := by
    change A = _ at hA
    rw [hA,show (H : Set (ZMod u)).toFinset={0,b} from hF]
    ext x
    simp only [Finset.vadd_finset_insert,Finset.vadd_finset_singleton,vadd_eq_add,add_zero,
      Finset.mem_union,Finset.mem_insert,Finset.mem_singleton]
    simp only [or_assoc]
  by_cases htlo : t₀.val < h
  · have he : A={0,(t₀.val : ZMod u),(h : ZMod u),((t₀.val+h : ℕ) : ZMod u)} := by
      simp only [Nat.cast_add,ZMod.natCast_zmod_val,←hbeq]
      rw [hA']
      ext x
      simp only [Finset.mem_insert,Finset.mem_singleton]
      simp only [or_left_comm]
    exact ⟨h,t₀.val,hu,htpos,htlo,generated_four_coprime hu A he hgen,he⟩
  · let t := t₀.val-h
    have ht : 0 < t ∧ t < h := by omega
    have ht₀ : t₀=((t+h : ℕ) : ZMod u) := by
      rw [Nat.sub_add_cancel (show h ≤ t₀.val by omega)]
      exact (ZMod.natCast_zmod_val t₀).symm
    have htb' : t₀+b=(t : ZMod u) := by
      rw [ht₀,hbeq,Nat.cast_add,add_assoc]
      have hh : (h : ZMod u)+(h : ZMod u)=0 := by rw [←hbeq]; exact hbb
      rw [hh,add_zero]
    have he : A={0,(t : ZMod u),(h : ZMod u),((t+h : ℕ) : ZMod u)} := by
      rw [hA',htb',ht₀,hbeq]
      ext x
      simp only [Finset.mem_insert,Finset.mem_singleton]
      simp only [or_left_comm,or_comm]
    exact ⟨h,t,hu,ht.1,ht.2,generated_four_coprime hu A he hgen,he⟩

theorem fourPoint_proper_growth {u : ℕ} [NeZero u] (A : Finset (ZMod u))
    (h0 : 0 ∈ A) (hA : A.card=4)
    (hgen : AddSubgroup.closure (A : Set (ZMod u))=⊤)
    (hnot : ¬CyclicAntipodal u A) (n : ℕ) (hproper : iteratedSum A (n+1) ≠ Finset.univ) :
    (iteratedSum A n).card+3 ≤ (iteratedSum A (n+1)).card := by
  by_contra hh
  have he := fourPoint_small_growth A h0 hA hgen n hproper (by omega)
  exact hnot (twoCoset_antipodal A hgen he.2)

theorem fourPoint_growth {u : ℕ} [NeZero u] (A : Finset (ZMod u))
    (h0 : 0 ∈ A) (hA : A.card=4)
    (hgen : AddSubgroup.closure (A : Set (ZMod u))=⊤)
    (hnot : ¬CyclicAntipodal u A) (n : ℕ) :
    min u (3*n+1) ≤ (iteratedSum A n).card := by
  induction n with
  | zero =>
    simp only [mul_zero,zero_add,iteratedSum_zero,Finset.card_singleton]
    exact min_le_right _ _
  | succ n ih =>
    by_cases hs : iteratedSum A (n+1)=Finset.univ
    · rw [hs,Finset.card_univ,ZMod.card]
      exact min_le_left _ _
    · have hg := fourPoint_proper_growth A h0 hA hgen hnot n hs
      have hcard : (iteratedSum A (n+1)).card < u := by
        have hh := Finset.card_lt_card
          (Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_univ _,hs⟩)
        simpa only [Finset.card_univ,ZMod.card] using hh
      omega
end NSP14.Additive
