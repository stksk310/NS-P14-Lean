module
public import NSP14.Endpoint.Minimal
@[expose] public section
set_option backward.isDefEq.respectTransparency false
namespace NSP14.Endpoint.Data
variable (D : NSP14.Endpoint.Data)

theorem minimal_word_zero_segment (w0 w1 w2 : List D.Variables)
    (hmin : Minimal (·∈D.coreFiber (D.coreCoordinates (D.coreWord (w0++(w1++w2)))).1)
      (D.coreCoordinates (D.coreWord (w0++(w1++w2)))).2)
    (hdiv : D.u∣D.coreOffset (D.coreWord w1)) : w1.length=0 := by
  let n := D.coreDegree (D.coreWord w1)
  let B := D.coreOffset (D.coreWord w1)
  let k := B/D.u
  have hB := D.corePoint_bound (D.coreWord w1).property
  change B≤D.u*n at hB
  have hkB : k*D.u=B := Nat.div_mul_cancel hdiv
  have hk : k≤n := by
    by_contra h
    have hnk : n+1≤k := by omega
    have hmul := Nat.mul_le_mul_left D.u hnk
    have hu := D.u_pos
    nlinarith
  have hpt : D.coreEndpointPoint (n-k,k)=D.coreWord w1 := by
    apply Subtype.ext
    rw [D.coreEndpointPoint_coe]
    apply Prod.ext
    · change n-k+k=n
      exact Nat.sub_add_cancel hk
    · change D.u*k=B
      nlinarith only [hkB]
  have hfac : D.coreWord (w0++(w1++w2))=
      D.coreWord (w0++w2)+D.coreEndpointPoint (n-k,k) := by
    rw [hpt]
    simp only [D.coreWord_append]
    abel
  have hz := D.minimal_endpoint_factor _ _ _ hmin hfac
  have hsum := congrArg (fun c : ℕ×ℕ => c.1+c.2) hz
  change n-k+k=0 at hsum
  have hn : n=0 := by omega
  have hlen := D.coreWord_degree w1
  change n=w1.length at hlen
  omega

/-- Equal prefix residues delete a genuine nonempty endpoint factor;
minimality forces the two prefix positions to coincide. -/
theorem minimal_prefix_eq (w : List D.Variables) (i j : ℕ) (hij : i≤j) (hj : j≤w.length)
    (hmod : D.coreOffset (D.coreWord (w.take i))%D.u=
      D.coreOffset (D.coreWord (w.take j))%D.u)
    (hmin : Minimal (·∈D.coreFiber (D.coreCoordinates (D.coreWord w)).1)
      (D.coreCoordinates (D.coreWord w)).2) : i=j := by
  let a := w.take i
  let b := (w.drop i).take (j-i)
  let c := w.drop j
  have htake : w.take j=a++b := by
    have h := List.take_add (l:=w) (i:=i) (j:=j-i)
    simpa only [Nat.add_sub_of_le hij] using h
  have htail : b++c=w.drop i := by
    have h := List.take_append_drop (j-i) (w.drop i)
    simpa only [List.drop_drop,Nat.add_sub_of_le hij] using h
  have hw : w=a++(b++c) := by
    rw [htail]
    exact (List.take_append_drop i w).symm
  have hpref : D.coreOffset (D.coreWord (w.take j))=
      D.coreOffset (D.coreWord a)+D.coreOffset (D.coreWord b) := by
    rw [htake,D.coreWord_append,(D.coreOffset).map_add]
  have he : D.coreOffset (D.coreWord a) ≡ D.coreOffset (D.coreWord (w.take j)) [MOD D.u] := hmod
  have hdiv := he.dvd'
  rw [hpref,Nat.add_sub_cancel_left] at hdiv
  have hmin' : Minimal (·∈D.coreFiber (D.coreCoordinates (D.coreWord (a++(b++c)))).1)
      (D.coreCoordinates (D.coreWord (a++(b++c)))).2 := by
    rw [← hw]
    exact hmin
  have hz := D.minimal_word_zero_segment a b c hmin' hdiv
  have hlen : b.length=j-i := by
    dsimp [b]
    rw [List.length_take,List.length_drop]
    exact min_eq_left (by omega)
  omega

def corePrefixResidue (w : List D.Variables) (i : Fin (w.length+1)) : Fin D.u :=
  ⟨D.coreOffset (D.coreWord (w.take i.val))%D.u,Nat.mod_lt _ D.u_pos⟩

theorem minimal_word_prefix_injective (w : List D.Variables)
    (hmin : Minimal (·∈D.coreFiber (D.coreCoordinates (D.coreWord w)).1)
      (D.coreCoordinates (D.coreWord w)).2) : Function.Injective (D.corePrefixResidue w) := by
  intro i j h
  apply Fin.ext
  have hm := congrArg Fin.val h
  by_cases hij : i.val≤j.val
  · exact D.minimal_prefix_eq w i.val j.val hij (by have := j.isLt;omega) hm hmin
  · exact (D.minimal_prefix_eq w j.val i.val (by omega) (by have := i.isLt;omega) hm.symm hmin).symm

theorem minimal_word_length_lt (w : List D.Variables)
    (hmin : Minimal (·∈D.coreFiber (D.coreCoordinates (D.coreWord w)).1)
      (D.coreCoordinates (D.coreWord w)).2) : w.length<D.u := by
  have h := Fintype.card_le_of_injective (D.corePrefixResidue w) (D.minimal_word_prefix_injective w hmin)
  simp only [Fintype.card_fin] at h
  omega
end NSP14.Endpoint.Data
