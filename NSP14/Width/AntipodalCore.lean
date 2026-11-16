module
public import NSP14.Width.FiveHigher
public import NSP14.Endpoint.CoreArtinBasis
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open scoped Classical BigOperators
namespace NSP14.Endpoint.Data
variable (D : NSP14.Endpoint.Data)

/-- A word in the three genuine internal generators of this same datum. -/
def antipodalPoint (h t : ℕ) (ha : D.a={t,h,t+h}) (x y z : ℕ) : D.corePoints :=
  x • D.coreGeneratorPoint (D.internalVariable ⟨t,by rw [ha]; simp⟩)+
  y • D.coreGeneratorPoint (D.internalVariable ⟨h,by rw [ha]; simp⟩)+
  z • D.coreGeneratorPoint (D.internalVariable ⟨t+h,by rw [ha]; simp⟩)

@[simp] theorem antipodalPoint_degree (h t : ℕ) (ha : D.a={t,h,t+h}) (x y z : ℕ) :
    D.coreDegree (D.antipodalPoint h t ha x y z)=x+y+z := by
  simp [antipodalPoint,coreDegree,coreGeneratorPoint,internalVariable]

@[simp] theorem antipodalPoint_offset (h t : ℕ) (ha : D.a={t,h,t+h}) (x y z : ℕ) :
    D.coreOffset (D.antipodalPoint h t ha x y z)=x*t+y*h+z*(t+h) := by
  simp [antipodalPoint,coreOffset,coreGeneratorPoint,internalVariable]

theorem antipodalPoint_coe (h t : ℕ) (ha : D.a={t,h,t+h}) (x y z : ℕ) :
    (D.antipodalPoint h t ha x y z).val=(x+y+z,x*t+y*h+z*(t+h)) := by
  apply Prod.ext
  · exact D.antipodalPoint_degree h t ha x y z
  · exact D.antipodalPoint_offset h t ha x y z

theorem minimal_antipodal_representation (h t : ℕ) (ha : D.a={t,h,t+h})
    (p : D.CoreMinimalIndex) : ∃ x y z : ℕ,p.val=D.antipodalPoint h t ha x y z := by
  obtain ⟨w,hw⟩ := D.exists_coreWord p.val
  have hint := D.minimal_word_internal w (by rw [hw]; exact p.property)
  have rep : ∀ w : List D.Variables,(∀ b∈w,b.val∈D.a) →
      ∃ x y z : ℕ,D.coreWord w=D.antipodalPoint h t ha x y z := by
    intro w
    induction w with
    | nil => exact fun _ => ⟨0,0,0,by simp [antipodalPoint]⟩
    | cons b w ih =>
      intro hint
      obtain ⟨x,y,z,hw⟩ := ih (fun c hc => hint c (List.mem_cons_of_mem b hc))
      have hb := hint b List.mem_cons_self
      rw [ha] at hb
      simp only [Finset.mem_insert,Finset.mem_singleton] at hb
      rcases hb with hb|hb|hb
      · refine ⟨x+1,y,z,?_⟩
        rw [D.coreWord_cons,hw]
        apply Subtype.ext
        change (1,b.val)+(D.antipodalPoint h t ha x y z).val=_
        rw [D.antipodalPoint_coe,D.antipodalPoint_coe,hb]
        apply Prod.ext <;> dsimp <;> ring
      · refine ⟨x,y+1,z,?_⟩
        rw [D.coreWord_cons,hw]
        apply Subtype.ext
        change (1,b.val)+(D.antipodalPoint h t ha x y z).val=_
        rw [D.antipodalPoint_coe,D.antipodalPoint_coe,hb]
        apply Prod.ext <;> dsimp <;> ring
      · refine ⟨x,y,z+1,?_⟩
        rw [D.coreWord_cons,hw]
        apply Subtype.ext
        change (1,b.val)+(D.antipodalPoint h t ha x y z).val=_
        rw [D.antipodalPoint_coe,D.antipodalPoint_coe,hb]
        apply Prod.ext <;> dsimp <;> ring
  obtain ⟨x,y,z,he⟩ := rep w hint
  exact ⟨x,y,z,hw.symm.trans he⟩

/-- The actual relations yz=xw, z²=xv and zw=vy exclude every
mixed word containing the middle offset h, in any coefficient field. -/
theorem antipodal_middle_isolated (h t : ℕ) (hu : D.u=2*h)
    (ha : D.a={t,h,t+h}) (x y z : ℕ)
    (hm : D.CoreMinimal (D.antipodalPoint h t ha x y z)) (hy : 0<y) :
    x=0 ∧ y=1 ∧ z=0 := by
  have hx : x=0 := by
    by_contra hx
    have hxp : 1 ≤ x := by omega
    have hyp : 1 ≤ y := by omega
    have hf : D.antipodalPoint h t ha x y z=
        D.antipodalPoint h t ha (x-1) (y-1) (z+1)+D.coreEndpointPoint (1,0) := by
      apply Subtype.ext
      change (D.antipodalPoint h t ha x y z).val=
        (D.antipodalPoint h t ha (x-1) (y-1) (z+1)).val+(D.coreEndpointPoint (1,0)).val
      rw [D.antipodalPoint_coe,D.antipodalPoint_coe,D.coreEndpointPoint_coe]
      have hxx := Nat.sub_add_cancel hxp
      have hyy := Nat.sub_add_cancel hyp
      apply Prod.ext <;> dsimp <;> nlinarith only [hxx,hyy]
    have hz := D.minimal_endpoint_factor _ _ _ hm hf
    have hz1 := congrArg Prod.fst hz
    norm_num at hz1
  have hz : z=0 := by
    by_contra hz
    have hzp : 1 ≤ z := by omega
    have hyp : 1 ≤ y := by omega
    have hf : D.antipodalPoint h t ha x y z=
        D.antipodalPoint h t ha (x+1) (y-1) (z-1)+D.coreEndpointPoint (0,1) := by
      apply Subtype.ext
      change (D.antipodalPoint h t ha x y z).val=
        (D.antipodalPoint h t ha (x+1) (y-1) (z-1)).val+(D.coreEndpointPoint (0,1)).val
      rw [D.antipodalPoint_coe,D.antipodalPoint_coe,D.coreEndpointPoint_coe,hu]
      have hzz := Nat.sub_add_cancel hzp
      have hyy := Nat.sub_add_cancel hyp
      apply Prod.ext <;> dsimp <;> nlinarith only [hzz,hyy]
    have he := D.minimal_endpoint_factor _ _ _ hm hf
    have he2 := congrArg Prod.snd he
    norm_num at he2
  have hy1 : y=1 := by
    by_contra hy1
    have hyp : 2 ≤ y := by omega
    have hf : D.antipodalPoint h t ha x y z=
        D.antipodalPoint h t ha x (y-2) z+D.coreEndpointPoint (1,1) := by
      apply Subtype.ext
      change (D.antipodalPoint h t ha x y z).val=
        (D.antipodalPoint h t ha x (y-2) z).val+(D.coreEndpointPoint (1,1)).val
      rw [D.antipodalPoint_coe,D.antipodalPoint_coe,D.coreEndpointPoint_coe,hu]
      have hyy := Nat.sub_add_cancel hyp
      apply Prod.ext <;> dsimp <;> nlinarith only [hyy]
    have he := D.minimal_endpoint_factor _ _ _ hm hf
    have he1 := congrArg Prod.fst he
    norm_num at he1
  exact ⟨hx,hy1,hz⟩


/-- Minimality is inherited by an actual additive factor of the core point. -/
theorem coreMinimal_add_left (p q : D.corePoints) (hm : D.CoreMinimal (p+q)) :
    D.CoreMinimal p := by
  by_contra hn
  rcases (D.core_not_minimal_iff_factor p).mp hn with ⟨r,hr⟩|⟨r,hr⟩
  · apply (D.core_not_minimal_iff_factor (p+q)).mpr (Or.inl ⟨r+q,by rw [hr]; abel⟩) hm
  · apply (D.core_not_minimal_iff_factor (p+q)).mpr (Or.inr ⟨r+q,by rw [hr]; abel⟩) hm

/-- Every pure y/w word of degree h has a genuine nonconstant endpoint
factor, with the possible isolated middle letter retained. -/
theorem antipodal_degree_h_not_minimal (h t : ℕ) (hu : D.u=2*h) (hh : 4 ≤ h)
    (ht : t<h) (ha : D.a={t,h,t+h}) (x z : ℕ) (hxz : x+z=h) :
    ¬D.CoreMinimal (D.antipodalPoint h t ha x 0 z) := by
  intro hm
  let K := (t+z)/2
  let r := (t+z)%2
  have hr : r<2 := Nat.mod_lt _ (by decide)
  have he : 2*K+r=t+z := by
    have := Nat.div_add_mod (t+z) 2
    dsimp [K,r]
    omega
  have hK : K<h := by dsimp [K]; omega
  have hle : r+K ≤ h := by omega
  have hf : D.antipodalPoint h t ha x 0 z=
      D.antipodalPoint h t ha 0 r 0+D.coreEndpointPoint (h-r-K,K) := by
    apply Subtype.ext
    change (D.antipodalPoint h t ha x 0 z).val=
      (D.antipodalPoint h t ha 0 r 0).val+(D.coreEndpointPoint (h-r-K,K)).val
    rw [D.antipodalPoint_coe,D.antipodalPoint_coe,D.coreEndpointPoint_coe,hu]
    apply Prod.ext
    · dsimp
      omega
    · dsimp
      nlinarith only [hxz,he]
  have hz := D.minimal_endpoint_factor _ _ _ hm hf
  have hz1 := congrArg Prod.fst hz
  have hz2 := congrArg Prod.snd hz
  change h-r-K=0 at hz1
  change K=0 at hz2
  omega

/-- The actual surviving pure words have degree strictly less than h. -/
theorem antipodal_pure_degree_lt (h t : ℕ) (hu : D.u=2*h) (hh : 4 ≤ h)
    (ht : t<h) (ha : D.a={t,h,t+h}) (x z : ℕ)
    (hm : D.CoreMinimal (D.antipodalPoint h t ha x 0 z)) : x+z<h := by
  by_contra hn
  let a := min x h
  let b := h-a
  have ha_le : a ≤ x := min_le_left _ _
  have ha_h : a ≤ h := min_le_right _ _
  have hb_le : b ≤ z := by dsimp [a,b]; omega
  have hab : a+b=h := by dsimp [b]; omega
  have hfac : D.antipodalPoint h t ha x 0 z=
      D.antipodalPoint h t ha a 0 b+D.antipodalPoint h t ha (x-a) 0 (z-b) := by
    apply Subtype.ext
    change (D.antipodalPoint h t ha x 0 z).val=
      (D.antipodalPoint h t ha a 0 b).val+(D.antipodalPoint h t ha (x-a) 0 (z-b)).val
    rw [D.antipodalPoint_coe,D.antipodalPoint_coe,D.antipodalPoint_coe]
    have hx := Nat.sub_add_cancel ha_le
    have hz := Nat.sub_add_cancel hb_le
    apply Prod.ext <;> dsimp <;> nlinarith only [hx,hz]
  rw [hfac] at hm
  exact D.antipodal_degree_h_not_minimal h t hu hh ht ha a b hab
    (D.coreMinimal_add_left _ _ hm)

/-- Every actual minimal basis vector is either the isolated h letter
or one of the bounded pure y/w words. -/
theorem antipodal_minimal_normal_form (h t : ℕ) (hu : D.u=2*h) (hh : 4 ≤ h)
    (ht : t<h) (ha : D.a={t,h,t+h}) (p : D.CoreMinimalIndex) :
    p.val=D.antipodalPoint h t ha 0 1 0 ∨
    ∃ x z : ℕ,x+z<h ∧ p.val=D.antipodalPoint h t ha x 0 z := by
  obtain ⟨x,y,z,he⟩ := D.minimal_antipodal_representation h t ha p
  have hm : D.CoreMinimal (D.antipodalPoint h t ha x y z) := he ▸ p.property
  by_cases hy : 0<y
  · obtain ⟨hx,hy,hz⟩ := D.antipodal_middle_isolated h t hu ha x y z hm hy
    left
    simpa only [hx,hy,hz] using he
  · have hy0 : y=0 := by omega
    right
    subst y
    exact ⟨x,z,D.antipodal_pure_degree_lt h t hu hh ht ha x z hm,he⟩


/-- Finite candidates are genuine core words. Nonminimal candidates map
back to the actual unit basis vector, rather than adding fictitious basis. -/
def antipodalCandidate (h t : ℕ) (ha : D.a={t,h,t+h}) :
    Option (Σ n : Fin h,Fin (n.val+1)) → D.corePoints
  | none => D.antipodalPoint h t ha 0 1 0
  | some ⟨n,z⟩ => D.antipodalPoint h t ha (n.val-z.val) 0 z.val

noncomputable def antipodalBasisMap (h t : ℕ) (ha : D.a={t,h,t+h})
    (i : Option (Σ n : Fin h,Fin (n.val+1))) : D.CoreMinimalIndex :=
  if hp : D.CoreMinimal (D.antipodalCandidate h t ha i) then
    ⟨D.antipodalCandidate h t ha i,hp⟩ else D.zeroMinimalIndex

theorem antipodalBasisMap_surjective (h t : ℕ) (hu : D.u=2*h) (hh : 4 ≤ h)
    (ht : t<h) (ha : D.a={t,h,t+h}) :
    Function.Surjective (D.antipodalBasisMap h t ha) := by
  intro p
  rcases D.antipodal_minimal_normal_form h t hu hh ht ha p with he|⟨x,z,hxz,he⟩
  · refine ⟨none,?_⟩
    have hp : D.CoreMinimal (D.antipodalCandidate h t ha none) := by
      change D.CoreMinimal (D.antipodalPoint h t ha 0 1 0)
      rw [←he]
      exact p.property
    apply Subtype.ext
    simp only [antipodalBasisMap,dite_eq_left hp]
    exact he.symm
  · let n : Fin h := ⟨x+z,hxz⟩
    let j : Fin (n.val+1) := ⟨z,by dsimp [n]; omega⟩
    let i : Option (Σ n : Fin h,Fin (n.val+1)) := some ⟨n,j⟩
    have hi : D.antipodalCandidate h t ha i=p.val := by
      dsimp [i,antipodalCandidate,n,j]
      rw [Nat.add_sub_cancel]
      exact he.symm
    have hp : D.CoreMinimal (D.antipodalCandidate h t ha i) := hi.symm ▸ p.property
    refine ⟨i,?_⟩
    apply Subtype.ext
    simp only [antipodalBasisMap,dite_eq_left hp]
    exact hi

theorem antipodalCandidate_card (h : ℕ) :
    Fintype.card (Option (Σ n : Fin h,Fin (n.val+1)))=(h+1).choose 2+1 := by
  rw [Fintype.card_option,Fintype.card_sigma]
  simp only [Fintype.card_fin]
  have hs := Fin.sum_univ_eq_sum_range (fun n : ℕ => n+1) h
  rw [hs]
  clear hs
  congr 1
  induction h with
  | zero => simp
  | succ h ih =>
    rw [Finset.sum_range_succ,ih]
    have hc := Nat.choose_succ_succ (h+1) 1
    change (h+1+1).choose 2=(h+1).choose 1+(h+1).choose 2 at hc
    rw [Nat.choose_one_right] at hc
    omega

/-- Actual QC dimension bound, valid without assuming t is a unit
modulo 2h and without replacing the original source by a group translate. -/
theorem antipodal_coreP_bound (k : Type) [Field k] (h t : ℕ) (hu : D.u=2*h)
    (hh : 4 ≤ h) (_ht0 : 0<t) (ht : t<h) (ha : D.a={t,h,t+h}) :
    D.coreP k ≤ (h+1).choose 2+1 := by
  rw [coreP,Module.finrank_eq_card_basis (D.QCoreBasis k)]
  have hc := Fintype.card_le_of_surjective (D.antipodalBasisMap h t ha)
    (D.antipodalBasisMap_surjective h t hu hh ht ha)
  rwa [antipodalCandidate_card] at hc
end NSP14.Endpoint.Data
