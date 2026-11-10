module
public import NSP14.ArithmeticSequence.Source
public import NSP14.Semigroup.Order
@[expose] public section
open scoped BigOperators Classical
namespace NSP14.ArithmeticSequence.Data
variable (D : NSP14.ArithmeticSequence.Data)

/-- The structured membership witness is an actual decomposition of precisely
l positive generators. This is not a numerical proxy for semigroup order. -/
theorem representation_hasLength (l j : ℕ) (hj : j ≤ D.v*l) :
    D.source.HasLength (l*D.m+j*D.d) l := by
  induction l generalizing j with
  | zero =>
    have hj0 : j=0 := by simpa using hj
    subst j
    simpa using D.source.length_zero
  | succ l ih =>
    let a := min D.v j
    let b := j-a
    have ha : a ≤ D.v := Nat.min_le_left _ _
    have haj : a ≤ j := Nat.min_le_right _ _
    have hb : b ≤ D.v*l := by
      dsimp [a,b]
      by_cases hv : D.v ≤ j
      · rw [min_eq_left hv]
        nlinarith [Nat.sub_add_cancel hv]
      · rw [min_eq_right (by omega : j ≤ D.v)]
        simp
    have h1 := D.source.length_one (D.generator_mem a ha)
      (by have := D.m_two;omega : 0 < D.m+a*D.d)
    have he : D.m+a*D.d+(l*D.m+b*D.d)=(l+1)*D.m+j*D.d := by
      have hba : b+a=j := Nat.sub_add_cancel haj
      nlinarith
    have h := D.source.length_add h1 (ih b hb)
    simpa only [he,Nat.add_comm 1 l] using h

/-- Longest decompositions use genuine minimal AP generators. -/
theorem order_representation {x : ℕ} (hx : x ∈ D.source) :
    ∃ j, j ≤ D.v*D.source.order x ∧ x=D.source.order x*D.m+j*D.d := by
  obtain ⟨f,hf,hs⟩ := D.source.order_realized_by_atoms hx
  choose i hi he using fun a => D.atom_eq_generator (hf a)
  refine ⟨∑ a,i a,?_,?_⟩
  · have h := Finset.sum_le_sum (fun a (_ : a ∈ (Finset.univ : Finset (Fin (D.source.order x)))) => hi a)
    simpa [Nat.mul_comm] using h
  · calc
      x = ∑ a, f a := hs.symm
      _ = D.source.order x*D.m+(∑ a,i a)*D.d := by
        simp_rw [he]
        simp [Finset.sum_add_distrib,Finset.sum_mul,Nat.mul_comm]

/-- Any canonical AP expression, with index below m, has its literal
coefficient of m as the maximum positive-element decomposition length. -/
theorem canonical_order (n i : ℕ) (hi : i < D.m) (hni : i ≤ D.v*n) :
    D.source.order (n*D.m+i*D.d)=n := by
  have hlen := D.representation_hasLength n i hni
  have hx : n*D.m+i*D.d ∈ D.source := ⟨n,i,hni,rfl⟩
  have hn := D.source.length_le_order hlen
  obtain ⟨j,hj,he⟩ := D.order_representation hx
  have hmod : i*D.d ≡ j*D.d [MOD D.m] := by
    change (i*D.d)%D.m=(j*D.d)%D.m
    have h := congrArg (fun x => x%D.m) he
    simpa only [Nat.add_mod,Nat.mul_mod_left,Nat.zero_add,Nat.mod_mod] using h
  have hc := hmod.cancel_right_of_coprime D.coprime.gcd_eq_one
  have himod : i=j%D.m := by
    change i%D.m=j%D.m at hc
    rwa [Nat.mod_eq_of_lt hi] at hc
  have hij : i ≤ j := by rw [himod];exact Nat.mod_le _ _
  have hm := D.m_two
  have hd := D.d_pos
  nlinarith

/-- Normalizing the index modulo m produces an actual canonical expression.
Its coefficient increases by q*d, which is why this works for every d≥1. -/
theorem canonical_representation {x : ℕ} (hx : x ∈ D.source) :
    ∃ n i, i < D.m ∧ i ≤ D.v*n ∧ x=n*D.m+i*D.d := by
  obtain ⟨l,j,hj,he⟩ := hx
  let q := j/D.m
  let i := j%D.m
  have hjq : i+q*D.m=j := by simpa only [i,q,Nat.mul_comm] using Nat.mod_add_div j D.m
  have hi : i < D.m := Nat.mod_lt _ (by have := D.m_two;omega)
  have hl : l ≤ l+q*D.d := Nat.le_add_right _ _
  have hni : i ≤ D.v*(l+q*D.d) :=
    (Nat.mod_le _ _).trans (hj.trans (Nat.mul_le_mul_left D.v hl))
  refine ⟨l+q*D.d,i,hi,hni,?_⟩
  nlinarith [he]

/-- AP tangent multiplication by the actual multiplicity is order stable.
In particular this supplies the semigroup input to x-regularity of its cone. -/
theorem order_add_m {x : ℕ} (hx : x ∈ D.source) :
    D.source.order (x+D.m)=D.source.order x+1 := by
  obtain ⟨n,i,hi,hni,he⟩ := D.canonical_representation hx
  have hni' : i ≤ D.v*(n+1) := hni.trans (Nat.mul_le_mul_left D.v (Nat.le_succ _))
  have hs : n*D.m+i*D.d+D.m=(n+1)*D.m+i*D.d := by ring
  rw [he,hs,D.canonical_order (n+1) i hi hni',D.canonical_order n i hi hni]
end NSP14.ArithmeticSequence.Data
