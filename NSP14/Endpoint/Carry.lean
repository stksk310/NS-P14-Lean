module
public import NSP14.Endpoint.Competitors
public import NSP14.Endpoint.Fibers
@[expose] public section
namespace NSP14.Endpoint.Data
variable (D : NSP14.Endpoint.Data)

def shiftedResidue (r : Fin D.u) (j : ℕ) : Fin D.u :=
  ⟨(r.val+j*D.m)%D.u,Nat.mod_lt _ D.u_pos⟩

def carry (r : Fin D.u) (j : ℕ) : ℕ := (r.val+j*D.m)/D.u

theorem carry_eq (r : Fin D.u) (j : ℕ) :
    r.val+j*D.m=(D.shiftedResidue r j).val+D.u*D.carry r j :=
  (Nat.mod_add_div (r.val+j*D.m) D.u).symm

theorem carry_pos (r : Fin D.u) (j : ℕ) (hj : 1≤j) : 1≤D.carry r j := by
  apply (Nat.le_div_iff_mul_le D.u_pos).mpr
  have hm := Nat.mul_le_mul_right D.m hj
  have := D.u_lt
  change 1*D.u≤r.val+j*D.m
  omega

theorem epsilon_le_one (r : Fin D.u) : D.epsilon r≤1 := by
  unfold epsilon
  split_ifs <;> omega

/-- Natural-number form of c-epsilon_r+epsilon_s >= floor(j*m/u),
so no signed contribution is lost by truncated subtraction. -/
theorem carry_epsilon_lower (r : Fin D.u) (j : ℕ) :
    j*D.m/D.u+D.epsilon r≤D.carry r j+D.epsilon (D.shiftedResidue r j) := by
  have hle : j*D.m/D.u≤D.carry r j :=
    Nat.div_le_div_right (Nat.le_add_left (j*D.m) r.val)
  by_cases he : D.carry r j=j*D.m/D.u
  · have hc := D.carry_eq r j
    have hd := Nat.mod_add_div (j*D.m) D.u
    rw [he] at hc
    have hrs : r.val≤(D.shiftedResidue r j).val := by omega
    by_cases hr : r.val=0
    · have hε : D.epsilon r=0 := by simp only [epsilon,hr,ite_true]
      rw [he,hε,add_zero]
      omega
    · have hs : (D.shiftedResidue r j).val≠0 := by omega
      simp only [epsilon,hr,hs,ite_false]
      omega
  · have hε := D.epsilon_le_one r
    omega

/-- The first coordinate is computed in Z and only then clamped. -/
def forbiddenStart (r : Fin D.u) (j : ℕ) (c : ℕ×ℕ) : ℕ×ℕ :=
  (((c.1 : ℤ)-(j*D.d+D.carry r j+D.epsilon (D.shiftedResidue r j) : ℕ)+
      (D.epsilon r : ℤ)).toNat,c.2+D.carry r j)

theorem forbiddenStart_first_le (r : Fin D.u) (j : ℕ) (c : ℕ×ℕ) (A : ℕ) :
    (D.forbiddenStart r j c).1≤A ↔
      c.1+D.epsilon r≤A+j*D.d+D.carry r j+D.epsilon (D.shiftedResidue r j) := by
  unfold forbiddenStart
  rw [Int.toNat_le]
  omega

theorem forbiddenStart_le (r : Fin D.u) (j : ℕ) (c p : ℕ×ℕ) :
    D.forbiddenStart r j c≤p ↔
      c.1+D.epsilon r≤p.1+j*D.d+D.carry r j+D.epsilon (D.shiftedResidue r j) ∧
        c.2+D.carry r j≤p.2 := by
  change (D.forbiddenStart r j c).1≤p.1 ∧ (D.forbiddenStart r j c).2≤p.2 ↔ _
  rw [D.forbiddenStart_first_le]
  rfl

theorem floor_jm_ge (j : ℕ) : j≤j*D.m/D.u := by
  apply (Nat.le_div_iff_mul_le D.u_pos).mpr
  exact Nat.mul_le_mul_left j D.u_lt.le

/-- Uniform decay, with Nat subtraction denoting max(H-2*j,0).
This proof applies to every m,d satisfying the broad EH. -/
theorem forbiddenStart_height (r : Fin D.u) (j L K H : ℕ) (hL : L≤H) :
    (D.forbiddenStart r j (L,K)).1≤H-2*j := by
  apply (D.forbiddenStart_first_le r j (L,K) (H-2*j)).mpr
  have hc := D.carry_epsilon_lower r j
  have hf := D.floor_jm_ge j
  have hd : j≤j*D.d := by simpa only [mul_one] using Nat.mul_le_mul_left j D.d_pos
  omega
end NSP14.Endpoint.Data
