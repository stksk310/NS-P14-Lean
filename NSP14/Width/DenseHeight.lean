module
public import NSP14.Width.DenseVolume
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open scoped Classical BigOperators
namespace NSP14.Endpoint.Data
variable (D : NSP14.Endpoint.Data)
/-- A prefix of length at least two in a surviving word cannot already
be a degree-one residue: replacing it gives a genuine endpoint factor. -/
theorem minimal_prefix_not_internal (w : List D.Variables)
    (hm : D.CoreMinimal (D.coreWord w)) (n : ℕ) (hn : 2 ≤ n) (hnw : n ≤ w.length) :
    D.coreOffset (D.coreWord (w.take n))%D.u  ∉  D.a := by
  intro ha
  let p := D.coreWord (w.take n)
  let B := D.coreOffset p
  let b := B%D.u
  let K := B/D.u
  have hbpos : 0<b := D.a_pos b ha
  have hb_lt : b<D.u := D.a_lt b ha
  have hB : B ≤ D.u*n := by
    have h := D.corePoint_bound p.property
    change B ≤ D.u*D.coreDegree p at h
    have hd : D.coreDegree p=n := by
      dsimp [p]
      rw [D.coreWord_degree,List.length_take,min_eq_left hnw]
    rwa [hd] at h
  have he : b+D.u*K=B := Nat.mod_add_div B D.u
  have hK : K<n := by have := D.u_pos; nlinarith
  let g := D.coreGeneratorPoint (D.internalVariable ⟨b,ha⟩)
  have hp : p=g+D.coreEndpointPoint (n-1-K,K) := by
    apply Subtype.ext
    change p.val=g.val+(D.coreEndpointPoint (n-1-K,K)).val
    rw [D.coreEndpointPoint_coe]
    apply Prod.ext
    · change D.coreDegree p=1+(n-1-K+K)
      dsimp [p]
      rw [D.coreWord_degree,List.length_take,min_eq_left hnw]
      omega
    · change B=b+D.u*K
      exact he.symm
  have hf : D.coreWord w=(D.coreWord (w.drop n)+g)+D.coreEndpointPoint (n-1-K,K) := by
    calc
      D.coreWord w = D.coreWord (w.take n)+D.coreWord (w.drop n) := by
        rw [←D.coreWord_append,List.take_append_drop]
      _ = _ := by change p+_=_; rw [hp]; abel
  have hz := D.minimal_endpoint_factor _ _ _ hm hf
  have hz1 := congrArg Prod.fst hz
  have hz2 := congrArg Prod.snd hz
  change n-1-K=0 at hz1
  change K=0 at hz2
  omega

/-- All prefixes after the first lie in distinct missing residues of the
same orientation. This bound does not require the dense hypothesis. -/
theorem minimal_word_missing_bound (w : List D.Variables)
    (hm : D.CoreMinimal (D.coreWord w)) : w.length ≤ D.u-D.q := by
  let f : Fin (w.length+1) → Fin D.u := D.corePrefixResidue w
  let A : Finset (Fin D.u) := D.a.attach.image (fun b => ⟨b.val,D.a_lt _ b.property⟩)
  have hA : A.card=D.q := by
    dsimp [A,q]
    rw [Finset.card_image_of_injective _ (by
      intro a b he
      apply Subtype.ext
      exact congrArg Fin.val he),Finset.card_attach]
  let I := Finset.univ.filter (fun i : Fin (w.length+1) => 2 ≤ i.val)
  have hf : Set.MapsTo f I ((Finset.univ\insert ⟨0,D.u_pos⟩ A : Finset (Fin D.u)) : Set (Fin D.u)) := by
    intro i hi
    have hi2 : 2 ≤ i.val := (Finset.mem_filter.mp hi).2
    have hiw : i.val ≤ w.length := by have := i.isLt; omega
    apply Finset.mem_sdiff.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    simp only [Finset.mem_insert,not_or]
    constructor
    · intro he
      have h0 : f i=f ⟨0,by omega⟩ := by
        change D.corePrefixResidue w i=D.corePrefixResidue w ⟨0,by omega⟩
        simpa only [corePrefixResidue,List.take_zero,coreWord_nil,map_zero,Nat.zero_mod] using (show D.corePrefixResidue w i=⟨0,D.u_pos⟩ from he)
      have heq := D.minimal_word_prefix_injective w hm h0
      have hv := congrArg Fin.val heq
      change i.val=0 at hv
      omega
    · rintro h
      obtain ⟨b,_,he⟩ := Finset.mem_image.mp h
      have hh := congrArg Fin.val he
      exact D.minimal_prefix_not_internal w hm i.val hi2 hiw (by
        change b.val=D.coreOffset (D.coreWord (w.take i.val))%D.u at hh
        rw [←hh]
        exact b.property)
  have hcard := Finset.card_le_card_of_injOn f hf
    (fun _ _ _ _ he => D.minimal_word_prefix_injective w hm he)
  have hzero : (⟨0,D.u_pos⟩ : Fin D.u) ∉ A := by
    rintro h
    obtain ⟨b,_,he⟩ := Finset.mem_image.mp h
    have hz := congrArg Fin.val he
    change b.val=0 at hz
    have hp := D.a_pos _ b.property
    omega
  rw [Finset.card_sdiff_of_subset (Finset.subset_univ _),Finset.card_univ,
    Fintype.card_fin,Finset.card_insert_of_notMem hzero,hA] at hcard
  have hI : I.card=w.length-1 := by
    have he : I=(Finset.univ\(Finset.univ.filter
        (fun i : Fin (w.length+1) => i.val<2))) := by ext i; simp [I]; omega
    rw [he,Finset.card_sdiff_of_subset (Finset.filter_subset _ _),Finset.card_univ,
      Fintype.card_fin]
    by_cases hw : 1 ≤ w.length
    · have htwo : (Finset.univ.filter (fun i : Fin (w.length+1) => i.val<2))=
          {⟨0,by omega⟩,⟨1,by omega⟩} := by
        ext i
        simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_insert,
          Finset.mem_singleton,Fin.ext_iff]
        omega
      rw [htwo]
      have hne : (⟨0,by omega⟩ : Fin (w.length+1)) ≠ ⟨1,by omega⟩ := by
        intro h
        have hh := congrArg Fin.val h
        change 0=1 at hh
        omega
      rw [Finset.card_pair hne]
      omega
    · have hz : w.length=0 := by omega
      have hall : (Finset.univ.filter (fun i : Fin (w.length+1) => i.val<2))=Finset.univ := by
        ext i
        simp only [Finset.mem_filter,Finset.mem_univ,true_and,iff_true]
        have := i.isLt
        omega
      rw [hall,Finset.card_univ,Fintype.card_fin,hz]
  have hqa : D.q+1 ≤ D.u := by
    have h := Finset.card_le_card (Finset.subset_univ (insert ⟨0,D.u_pos⟩ A))
    rw [Finset.card_insert_of_notMem hzero,hA,Finset.card_univ,Fintype.card_fin] at h
    exact h
  rw [hI] at hcard
  omega

/-- Hx in the original coordinate direction, without reflecting the core. -/
theorem coreHeight_le_missing : D.coreHeight ≤ D.u-D.q-1 := by
  apply Finset.sup_le
  intro r _
  apply Finset.sup_le
  intro c hc
  have hm := (D.mem_minimalPoints r c).mp hc
  by_cases hr : r.val=0
  · have he : r=⟨0,D.u_pos⟩ := Fin.ext hr
    subst r
    rw [D.minimalFiber_zero c hm]
    exact Nat.zero_le _
  obtain ⟨w,hw,_,_⟩ := D.exists_minimal_internal_word r c hm
  have hwm : D.CoreMinimal (D.coreWord w) := by
    change Minimal (· ∈ D.coreFiber (D.coreCoordinates (D.coreWord w)).1)
      (D.coreCoordinates (D.coreWord w)).2
    rw [hw]
    exact hm
  have hlen := D.minimal_word_missing_bound w hwm
  have hd := D.decode_coreCoordinates (D.coreWord w)
  rw [hw] at hd
  have hdeg := congrArg Prod.fst hd
  change c.1+c.2+D.epsilon r=D.coreDegree (D.coreWord w) at hdeg
  rw [D.coreWord_degree] at hdeg
  simp only [epsilon,hr,ite_false] at hdeg
  omega
end NSP14.Endpoint.Data
