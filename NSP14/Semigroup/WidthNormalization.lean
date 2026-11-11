module
public import NSP14.Endpoint.Data
@[expose] public section
open scoped Classical
namespace NSP14.NumericalSemigroup
variable (S : NumericalSemigroup)

theorem atoms_gcd_one : S.atoms.gcd id=1 := by
  have hdiv {n : ℕ} (hn : n∈S) : S.atoms.gcd id∣n := by
    apply AddSubmonoid.closure_induction (motive:=fun n _ => S.atoms.gcd id∣n) ?_ (dvd_zero _) ?_ (S.mem_closure_atoms hn)
    · intro x hx;exact Finset.gcd_dvd hx
    · intro x y _ _ hx hy;exact dvd_add hx hy
  apply Nat.dvd_one.mp
  exact (Nat.dvd_add_iff_right (hdiv (S.cofinite S.conductor le_rfl))).mpr
    (hdiv (S.cofinite (S.conductor+1) (by omega)))

noncomputable def atomOffsets : Finset ℕ := S.atoms.image (fun a => a-S.multiplicity)
noncomputable def offsetGcd : ℕ := S.atomOffsets.gcd id

@[simp] theorem zero_mem_atomOffsets : 0∈S.atomOffsets := by
  exact Finset.mem_image.mpr ⟨S.multiplicity,S.multiplicity_mem_atoms,by simp⟩

theorem width_mem_atomOffsets : S.width∈S.atomOffsets :=
  Finset.mem_image.mpr ⟨S.maxAtom,Finset.max'_mem _ _,rfl⟩

theorem atomOffset_le_width {b : ℕ} (hb : b∈S.atomOffsets) : b≤S.width := by
  obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hb
  exact Nat.sub_le_sub_right (S.atom_le_maxAtom ha) _

theorem offsetGcd_dvd {b : ℕ} (hb : b∈S.atomOffsets) : S.offsetGcd∣b := Finset.gcd_dvd hb

theorem offsetGcd_pos (he : 2≤S.embeddingDimension) : 0 < S.offsetGcd := by
  have hw := S.width_pos he
  have hd := S.offsetGcd_dvd S.width_mem_atomOffsets
  by_contra h
  have h0 : S.offsetGcd=0 := by omega
  rw [h0,zero_dvd_iff] at hd
  omega

theorem offsetGcd_coprime : Nat.Coprime S.multiplicity S.offsetGcd := by
  change Nat.gcd S.multiplicity S.offsetGcd=1
  apply Nat.dvd_one.mp
  rw [← S.atoms_gcd_one]
  apply Finset.dvd_gcd
  intro a ha
  have hm : S.multiplicity≤a := S.multiplicity_le (S.atoms_mem ha) ((S.mem_atoms_iff _).mp ha).2.1
  have hd := S.offsetGcd_dvd (Finset.mem_image.mpr ⟨a,ha,rfl⟩)
  have hg : Nat.gcd S.multiplicity S.offsetGcd∣a-S.multiplicity :=
    (Nat.gcd_dvd_right _ _).trans hd
  have h := dvd_add (Nat.gcd_dvd_left S.multiplicity S.offsetGcd) hg
  simpa only [id,Nat.add_sub_of_le hm] using h

theorem atomOffsets_card : S.atomOffsets.card=S.embeddingDimension := by
  unfold atomOffsets embeddingDimension
  apply Finset.card_image_of_injOn
  intro a ha b hb he
  change a-S.multiplicity=b-S.multiplicity at he
  have ha' := S.multiplicity_le (S.atoms_mem ha) ((S.mem_atoms_iff _).mp ha).2.1
  have hb' := S.multiplicity_le (S.atoms_mem hb) ((S.mem_atoms_iff _).mp hb).2.1
  omega

noncomputable def normalizedOffsets : Finset ℕ := S.atomOffsets.image (fun b => b/S.offsetGcd)
noncomputable def normalizedWidth : ℕ := S.width/S.offsetGcd
noncomputable def internalOffsets : Finset ℕ := (S.normalizedOffsets.erase 0).erase S.normalizedWidth

theorem width_factor : S.normalizedWidth*S.offsetGcd=S.width :=
  Nat.div_mul_cancel (S.offsetGcd_dvd S.width_mem_atomOffsets)

@[simp] theorem zero_mem_normalizedOffsets : 0∈S.normalizedOffsets := by
  exact Finset.mem_image.mpr ⟨0,S.zero_mem_atomOffsets,by simp⟩

theorem normalizedWidth_mem : S.normalizedWidth∈S.normalizedOffsets :=
  Finset.mem_image.mpr ⟨S.width,S.width_mem_atomOffsets,rfl⟩

theorem normalizedOffset_factor {b : ℕ} (hb : b∈S.normalizedOffsets) :
    b*S.offsetGcd∈S.atomOffsets := by
  obtain ⟨c,hc,rfl⟩ := Finset.mem_image.mp hb
  simpa only [Nat.div_mul_cancel (S.offsetGcd_dvd hc)] using hc

theorem normalizedOffset_le {b : ℕ} (hb : b∈S.normalizedOffsets) : b≤S.normalizedWidth := by
  obtain ⟨c,hc,rfl⟩ := Finset.mem_image.mp hb
  exact Nat.div_le_div_right (S.atomOffset_le_width hc)

theorem normalizedWidth_pos (he : 2≤S.embeddingDimension) : 0<S.normalizedWidth := by
  have := S.width_pos he
  have := S.width_factor
  nlinarith

theorem normalizedOffsets_gcd_one (he : 2≤S.embeddingDimension) : S.normalizedOffsets.gcd id=1 := by
  rw [normalizedOffsets,Finset.gcd_image]
  exact Finset.gcd_div_id_eq_one S.width_mem_atomOffsets (by have := S.width_pos he;omega)

theorem normalizedOffsets_card : S.normalizedOffsets.card=S.embeddingDimension := by
  rw [normalizedOffsets,← S.atomOffsets_card]
  apply Finset.card_image_of_injOn
  intro a ha b hb h
  change a/S.offsetGcd=b/S.offsetGcd at h
  have ha' := Nat.div_mul_cancel (S.offsetGcd_dvd ha)
  have hb' := Nat.div_mul_cancel (S.offsetGcd_dvd hb)
  rw [h] at ha'
  omega

theorem internalOffsets_card (he : 2≤S.embeddingDimension) : S.internalOffsets.card=S.embeddingDimension-2 := by
  rw [internalOffsets,Finset.card_erase_of_mem (Finset.mem_erase.mpr
    ⟨Nat.ne_of_gt (S.normalizedWidth_pos he),S.normalizedWidth_mem⟩),
    Finset.card_erase_of_mem S.zero_mem_normalizedOffsets,S.normalizedOffsets_card,Nat.sub_sub]

theorem internalOffsets_pos {b : ℕ} (hb : b∈S.internalOffsets) : 0<b := by
  exact Nat.pos_of_ne_zero (Finset.mem_erase.mp (Finset.mem_erase.mp hb).2).1

theorem internalOffsets_lt {b : ℕ} (hb : b∈S.internalOffsets) : b<S.normalizedWidth := by
  have hne := (Finset.mem_erase.mp hb).1
  have hmem := (Finset.mem_erase.mp (Finset.mem_erase.mp hb).2).2
  have := S.normalizedOffset_le hmem
  omega

theorem internalOffsets_coprime (he : 2≤S.embeddingDimension) :
    Nat.gcd (S.internalOffsets.gcd id) S.normalizedWidth=1 := by
  apply Nat.dvd_one.mp
  rw [← S.normalizedOffsets_gcd_one he]
  apply Finset.dvd_gcd
  intro b hb
  by_cases h0 : b=0
  · rw [h0];exact dvd_zero _
  by_cases hu : b=S.normalizedWidth
  · rw [hu];exact Nat.gcd_dvd_right _ _
  exact (Nat.gcd_dvd_left _ _).trans (Finset.gcd_dvd
    (Finset.mem_erase.mpr ⟨hu,Finset.mem_erase.mpr ⟨h0,hb⟩⟩))
end NSP14.NumericalSemigroup

namespace NSP14.NumericalSemigroup
variable (S : NumericalSemigroup)

theorem offsets_reconstruct :
    insert 0 (insert S.normalizedWidth S.internalOffsets)=S.normalizedOffsets := by
  ext b
  by_cases h0 : b=0
  · subst b;simp
  by_cases hu : b=S.normalizedWidth
  · subst b;simp [S.normalizedWidth_mem]
  simp [internalOffsets,h0,hu]

/-- Normalize the actual minimal atoms of a narrow source. The original
multiplicity is preserved; it is never divided by the dilation. -/
noncomputable def endpointData (he : 4≤S.embeddingDimension) (hw : S.width≤S.multiplicity-2) :
    NSP14.Endpoint.Data where
  m := S.multiplicity
  d := S.offsetGcd
  u := S.normalizedWidth
  a := S.internalOffsets
  q_two := by rw [S.internalOffsets_card (by omega)];omega
  a_pos := fun _ h => S.internalOffsets_pos h
  a_lt := fun _ h => S.internalOffsets_lt h
  u_lt := by
    have hm := he.trans S.embeddingDimension_le_multiplicity
    have hdiv := Nat.div_le_self S.width S.offsetGcd
    change S.width/S.offsetGcd<S.multiplicity
    omega
  d_pos := S.offsetGcd_pos (by omega)
  offsets_coprime := S.internalOffsets_coprime (by omega)
  coprime := S.offsetGcd_coprime

theorem endpointData_m (he : 4≤S.embeddingDimension) (hw : S.width≤S.multiplicity-2) :
    (S.endpointData he hw).m=S.multiplicity := rfl

theorem endpointData_embedding (he : 4≤S.embeddingDimension) (hw : S.width≤S.multiplicity-2) :
    (S.endpointData he hw).q+2=S.embeddingDimension := by
  change S.internalOffsets.card+2=S.embeddingDimension
  rw [S.internalOffsets_card (by omega)]
  omega

theorem endpointData_narrow (he : 4≤S.embeddingDimension) (hw : S.width≤S.multiplicity-2) :
    (S.endpointData he hw).d*(S.endpointData he hw).u+2≤(S.endpointData he hw).m := by
  change S.offsetGcd*S.normalizedWidth+2≤S.multiplicity
  have h := S.width_factor
  have hm := he.trans S.embeddingDimension_le_multiplicity
  have hw' : S.width+2≤S.multiplicity := by omega
  nlinarith only [h,hw']

theorem endpointData_generators (he : 4≤S.embeddingDimension) (hw : S.width≤S.multiplicity-2) :
    (S.endpointData he hw).generators=S.atoms := by
  have hoff : (S.endpointData he hw).offsets=S.normalizedOffsets := S.offsets_reconstruct
  unfold NSP14.Endpoint.Data.generators
  rw [hoff]
  ext n
  constructor
  · intro hn
    obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hn
    have hB := S.normalizedOffset_factor hb
    obtain ⟨a,ha,heq⟩ := Finset.mem_image.mp hB
    have hm := S.multiplicity_le (S.atoms_mem ha) ((S.mem_atoms_iff _).mp ha).2.1
    change S.multiplicity+b*S.offsetGcd∈S.atoms
    rw [← heq,Nat.add_sub_of_le hm]
    exact ha
  · intro hn
    have hm := S.multiplicity_le (S.atoms_mem hn) ((S.mem_atoms_iff _).mp hn).2.1
    have hB : n-S.multiplicity∈S.atomOffsets := Finset.mem_image.mpr ⟨n,hn,rfl⟩
    refine Finset.mem_image.mpr ⟨(n-S.multiplicity)/S.offsetGcd,
      Finset.mem_image.mpr ⟨n-S.multiplicity,hB,rfl⟩,?_⟩
    change S.multiplicity+(n-S.multiplicity)/S.offsetGcd*S.offsetGcd=n
    rw [Nat.div_mul_cancel (S.offsetGcd_dvd hB),Nat.add_sub_of_le hm]

theorem endpointData_carrier (he : 4≤S.embeddingDimension) (hw : S.width≤S.multiplicity-2) :
    (S.endpointData he hw).source.carrier=S.carrier := by
  change AddSubmonoid.closure ((S.endpointData he hw).generators : Set ℕ)=S.carrier
  rw [S.endpointData_generators he hw,S.closure_atoms]
end NSP14.NumericalSemigroup
