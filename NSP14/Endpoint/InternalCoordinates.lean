module
public import NSP14.Endpoint.CoreInternalAction
@[expose] public section
set_option backward.isDefEq.respectTransparency false
namespace NSP14.Endpoint.Data
variable (D : Data)

/-- Exact carry formula in the fixed orientation. Subtractions are
legitimate because the destination is an actual nonnegative core point. -/
theorem internal_coordinate_step (b : D.a) (p : D.corePoints) (r s : Fin D.u) (L K c : ℕ)
    (hp : D.coreCoordinates p=(r,L,K)) (hc : r.val+b.val=s.val+D.u*c) :
    D.coreCoordinates (p+D.coreGeneratorPoint (D.internalVariable b))=
      (s,L+1+D.epsilon r-c-D.epsilon s,K+c) := by
  let p' := p+D.coreGeneratorPoint (D.internalVariable b)
  obtain ⟨t,A,B,ht⟩ : ∃ t A B,D.coreCoordinates p'=(t,A,B) := ⟨_,_,_,rfl⟩
  have hbase := D.decode_coreCoordinates p
  rw [hp] at hbase
  have hn : L+K+D.epsilon r=D.coreDegree p := congrArg Prod.fst hbase
  have hB : r.val+D.u*K=D.coreOffset p := congrArg Prod.snd hbase
  have hnew := D.decode_coreCoordinates p'
  rw [ht] at hnew
  have hn' : A+B+D.epsilon t=D.coreDegree p+1 := congrArg Prod.fst hnew
  have hB' : t.val+D.u*B=D.coreOffset p+b.val := congrArg Prod.snd hnew
  have hs : t=s := by
    apply Fin.ext
    have hm := congrArg (fun n : ℕ => n%D.u) hB'
    rw [←hB] at hm
    have hh : r.val+D.u*K+b.val=s.val+D.u*(K+c) := by nlinarith [hc]
    rw [hh] at hm
    simpa only [Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt t.isLt,Nat.mod_eq_of_lt s.isLt] using hm
  subst t
  have hK : B=K+c := by nlinarith [D.u_pos]
  have hL : A=L+1+D.epsilon r-c-D.epsilon s := by omega
  change D.coreCoordinates p'= _
  rw [ht,hK,hL]
end NSP14.Endpoint.Data
