module
public import NSP14.Endpoint.CoreKernel
@[expose] public section
set_option backward.isDefEq.respectTransparency false
namespace NSP14.Endpoint.Data
variable (D : NSP14.Endpoint.Data)

def epsilon (r : Fin D.u) : ℕ := if r.val=0 then 0 else 1
abbrev Coordinate := Fin D.u×ℕ×ℕ

def decodeCoordinate (c : D.Coordinate) : ℕ×ℕ :=
  (c.2.1+c.2.2+D.epsilon c.1,c.1.val+D.u*c.2.2)

def residue (p : D.corePoints) : Fin D.u := ⟨p.val.2%D.u,Nat.mod_lt _ D.u_pos⟩

theorem coordinate_budget (p : D.corePoints) : p.val.2/D.u+D.epsilon (D.residue p)≤p.val.1 := by
  have hd := Nat.mod_add_div p.val.2 D.u
  have hb := D.corePoint_bound p.property
  have hu := D.u_pos
  change p.val.2/D.u+(if p.val.2%D.u=0 then 0 else 1)≤p.val.1
  split_ifs with h0
  · by_contra h
    have hk : p.val.1+1≤p.val.2/D.u := by omega
    have hmul := Nat.mul_le_mul_left D.u hk
    nlinarith
  · by_contra h
    have hk : p.val.1≤p.val.2/D.u := by omega
    have hmul := Nat.mul_le_mul_left D.u hk
    have hr : 0 < p.val.2%D.u := Nat.pos_of_ne_zero h0
    nlinarith

def coreCoordinates (p : D.corePoints) : D.Coordinate :=
  (D.residue p,p.val.1-p.val.2/D.u-D.epsilon (D.residue p),p.val.2/D.u)

theorem decode_coreCoordinates (p : D.corePoints) : D.decodeCoordinate (D.coreCoordinates p)=p.val := by
  apply Prod.ext
  · change p.val.1-p.val.2/D.u-D.epsilon (D.residue p)+p.val.2/D.u+D.epsilon (D.residue p)=p.val.1
    have := D.coordinate_budget p
    omega
  · exact Nat.mod_add_div p.val.2 D.u

theorem decodeCoordinate_injective : Function.Injective D.decodeCoordinate := by
  rintro ⟨r,L,K⟩ ⟨s,A,B⟩ h
  have he : r.val+D.u*K=s.val+D.u*B := congrArg Prod.snd h
  have hr : r=s := by
    apply Fin.ext
    have hm := congrArg (fun n => n%D.u) he
    simpa only [Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt r.isLt,Nat.mod_eq_of_lt s.isLt] using hm
  subst s
  have hk : K=B := Nat.eq_of_mul_eq_mul_left D.u_pos (by omega)
  subst B
  have hL : L=A := by
    have hn := congrArg Prod.fst h
    change L+K+D.epsilon r=A+K+D.epsilon r at hn
    omega
  subst A
  rfl

/-- The indices are actual core points in these nonnegative coordinates.
No claim that all triples occur, or that residues are subalgebras. -/
def CoordinatePoint := {c : D.Coordinate // D.decodeCoordinate c∈D.corePoints}

def coreCoordinateEquiv : D.corePoints ≃ D.CoordinatePoint where
  toFun p := ⟨D.coreCoordinates p,by rw [D.decode_coreCoordinates];exact p.property⟩
  invFun c := ⟨D.decodeCoordinate c.val,c.property⟩
  left_inv p := Subtype.ext (D.decode_coreCoordinates p)
  right_inv c := by
    apply Subtype.ext
    apply D.decodeCoordinate_injective
    exact D.decode_coreCoordinates ⟨D.decodeCoordinate c.val,c.property⟩
end NSP14.Endpoint.Data
