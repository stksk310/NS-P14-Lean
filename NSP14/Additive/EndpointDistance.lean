module
public import NSP14.Additive.EndpointResidues
public import NSP14.Additive.CyclicGrowth
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open scoped Classical Pointwise BigOperators
namespace NSP14.Endpoint.Data
variable (D : NSP14.Endpoint.Data)
def residueIndex (r : ZMod D.u) : Fin D.u := ⟨r.val,ZMod.val_lt r⟩
theorem residueIndex_natCast (r : Fin D.u) : D.residueIndex (r.val : ZMod D.u) = r := by
  apply Fin.ext
  exact ZMod.val_natCast_of_lt r.isLt
def residueIndexEquiv : ZMod D.u ≃ Fin D.u where
  toFun := D.residueIndex
  invFun r := (r.val : ZMod D.u)
  left_inv r := ZMod.natCast_zmod_val r
  right_inv r := D.residueIndex_natCast r

theorem residue_distance_iff (n : ℕ) (r : ZMod D.u) :
    r ∈ NSP14.Additive.iteratedSum D.residueAlphabet n ↔
      D.shortestDegree (D.residueIndex r) ≤ n := by
  constructor
  · intro hr
    obtain ⟨p,hp,hpr⟩ := (D.residueAlphabet_iterated_core n r).mp hr
    have hindex : (D.coreCoordinates p).1 = D.residueIndex r := by
      apply Fin.ext
      change D.coreOffset p % D.u = r.val
      have hh := congrArg ZMod.val hpr
      simpa only [ZMod.val_natCast] using hh
    have hm := D.coordinate_mem_fiber p
    rw [hindex] at hm
    have hh := D.shortestDegree_le (D.residueIndex r) (D.coreCoordinates p).2 hm
    have hd := congrArg Prod.fst (D.decode_coreCoordinates p)
    change (D.coreCoordinates p).2.1+(D.coreCoordinates p).2.2+
      D.epsilon (D.coreCoordinates p).1=D.coreDegree p at hd
    rw [hindex,hp] at hd
    omega
  · intro hn
    let s := D.residueIndex r
    let c := D.shortestPoint s
    let p : D.corePoints := ⟨D.decodeCoordinate (s,c),D.shortestPoint_mem s⟩
    have hp : D.coreDegree p = D.shortestDegree s := D.shortestPoint_degree s
    have hpr : (D.coreOffset p : ZMod D.u) = r := by
      change ((s.val+D.u*c.2 : ℕ) : ZMod D.u)=r
      rw [Nat.cast_add,Nat.cast_mul,ZMod.natCast_self,zero_mul,add_zero]
      exact ZMod.natCast_zmod_val r
    have hm := (D.residueAlphabet_iterated_core (D.shortestDegree s) r).mpr ⟨p,hp,hpr⟩
    exact NSP14.Additive.iteratedSum_subset_of_le D.zero_mem_residueAlphabet hn hm

theorem residueAlphabet_generates : AddSubgroup.closure (D.residueAlphabet : Set (ZMod D.u)) = ⊤ := by
  apply top_unique
  intro r _
  have hr := (D.residue_distance_iff (D.shortestDegree (D.residueIndex r)) r).mpr le_rfl
  have hall (n : ℕ) : ∀ x ∈ NSP14.Additive.iteratedSum D.residueAlphabet n,
      x ∈ AddSubgroup.closure (D.residueAlphabet : Set (ZMod D.u)) := by
    induction n with
    | zero => intro x hx; rw [Finset.mem_singleton.mp hx]; exact AddSubgroup.zero_mem _
    | succ n ih =>
      intro x hx
      obtain ⟨a,ha,b,hb,rfl⟩ := Finset.mem_add.mp hx
      exact AddSubgroup.add_mem _ (ih a ha) (AddSubgroup.subset_closure hb)
  exact hall _ r hr

theorem residueAlphabet_saturated (n : ℕ) (hn : D.u-1 ≤ n) :
    NSP14.Additive.iteratedSum D.residueAlphabet n = Finset.univ := by
  apply Finset.eq_univ_iff_forall.mpr
  intro r
  rw [D.residue_distance_iff]
  have hh := D.shortestDegree_lt (D.residueIndex r)
  omega
end NSP14.Endpoint.Data
