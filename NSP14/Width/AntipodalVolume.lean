module
public import NSP14.Width.AntipodalBasis
public import NSP14.Additive.EndpointDistance
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open scoped Classical BigOperators
namespace NSP14.Endpoint.Data
variable (D : NSP14.Endpoint.Data)

def antipodalResidue (h t : ℕ) (i : Fin h × Fin 2) : Fin D.u :=
  ⟨(i.1.val*t+i.2.val*h)%D.u,Nat.mod_lt _ D.u_pos⟩

theorem antipodalResidue_injective (h t : ℕ) (hu : D.u=2*h) (hh : 0<h)
    (hc : Nat.Coprime t h) : Function.Injective (D.antipodalResidue h t) := by
  rintro ⟨n,e⟩ ⟨m,f⟩ he
  have hm : n.val*t+e.val*h ≡ m.val*t+f.val*h [MOD D.u] := congrArg Fin.val he
  have hdvd : h∣D.u := by rw [hu]; exact dvd_mul_left _ _
  have hm' := hm.of_dvd hdvd
  change (n.val*t+e.val*h)%h=(m.val*t+f.val*h)%h at hm'
  simp only [Nat.add_mul_mod_self_right] at hm'
  have hnm : n=m := by
    have hmod : n.val*t ≡ m.val*t [MOD h] := by exact hm'
    have hn := hmod.cancel_right_of_coprime hc.symm.gcd_eq_one
    change n.val%h=m.val%h at hn
    rw [Nat.mod_eq_of_lt n.isLt,Nat.mod_eq_of_lt m.isLt] at hn
    exact Fin.ext hn
  subst m
  have hef := Nat.ModEq.add_left_cancel' (n.val*t) hm
  change (e.val*h)%D.u=(f.val*h)%D.u at hef
  have he2 := e.isLt
  have hf2 := f.isLt
  rw [Nat.mod_eq_of_lt (by nlinarith only [he2,hh,hu]),
    Nat.mod_eq_of_lt (by nlinarith only [hf2,hh,hu])] at hef
  have hef' : e=f := Fin.ext (by nlinarith only [hef,hh])
  subst f
  rfl

noncomputable def antipodalResidueEquiv (h t : ℕ) (hu : D.u=2*h) (hh : 0<h)
    (hc : Nat.Coprime t h) : (Fin h × Fin 2) ≃ Fin D.u :=
  Equiv.ofBijective (D.antipodalResidue h t)
    ((Fintype.bijective_iff_injective_and_card _).mpr
      ⟨D.antipodalResidue_injective h t hu hh hc,by
        rw [Fintype.card_prod,Fintype.card_fin,Fintype.card_fin,Fintype.card_fin]
        omega⟩)

theorem antipodal_shortest_positive (h t : ℕ) (hu : D.u=2*h) (hc : Nat.Coprime t h)
    (ha : D.a={t,h,t+h}) (n : Fin h) (e : Fin 2) (hn : 0<n.val) :
    D.shortestDegree (D.antipodalResidue h t (n,e))=n.val := by
  let r := D.antipodalResidue h t (n,e)
  have he_le : e.val ≤ n.val := by have := e.isLt; omega
  let p := D.antipodalPoint h t ha (n.val-e.val) 0 e.val
  have hpd : D.coreDegree p=n.val := by
    dsimp [p]
    rw [D.antipodalPoint_degree]
    omega
  have hpi : (D.coreCoordinates p).1=r := by
    apply Fin.ext
    change D.coreOffset p%D.u=(n.val*t+e.val*h)%D.u
    dsimp [p]
    rw [D.antipodalPoint_offset]
    congr 1
    have he := Nat.sub_add_cancel he_le
    nlinarith only [he]
  have hupp : D.shortestDegree r ≤ n.val := by
    have h := D.shortestDegree_le (D.coreCoordinates p).1 (D.coreCoordinates p).2 (D.coordinate_mem_fiber p)
    have hd := congrArg Prod.fst (D.decode_coreCoordinates p)
    change (D.coreCoordinates p).2.1+(D.coreCoordinates p).2.2+
      D.epsilon (D.coreCoordinates p).1=D.coreDegree p at hd
    rw [hpi] at h hd
    omega
  let c := D.shortestPoint r
  let q : D.corePoints := ⟨D.decodeCoordinate (r,c),D.shortestPoint_mem r⟩
  have hqd : D.coreDegree q=D.shortestDegree r := D.shortestPoint_degree r
  obtain ⟨l,j,hl,hB⟩ := D.antipodal_mod_representation h t hu ha q
  have hm : D.coreOffset q ≡ n.val*t+e.val*h [MOD D.u] := by
    change (r.val+D.u*c.2)%D.u=(n.val*t+e.val*h)%D.u
    rw [Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt r.isLt]
    rfl
  have hdvd : h∣D.u := by rw [hu]; exact dvd_mul_left _ _
  have hm' := hm.of_dvd hdvd
  rw [hB] at hm'
  change (l*t+j*h)%h=(n.val*t+e.val*h)%h at hm'
  simp only [Nat.add_mul_mod_self_right] at hm'
  have heq : l ≡ n.val [MOD h] := Nat.ModEq.cancel_right_of_coprime hc.symm.gcd_eq_one hm'
  change l%h=n.val%h at heq
  have hll : l<h := by rw [hqd] at hl; have := n.isLt; omega
  rw [Nat.mod_eq_of_lt hll,Nat.mod_eq_of_lt n.isLt] at heq
  rw [hqd] at hl
  change D.shortestDegree r=n.val
  exact Nat.le_antisymm hupp (heq ▸ hl)

theorem antipodal_shortest_zero (h t : ℕ) (hu : D.u=2*h) (hh : 0<h)
    (ha : D.a={t,h,t+h}) (e : Fin 2) :
    D.shortestDegree (D.antipodalResidue h t (⟨0,hh⟩,e))=e.val := by
  have he := e.isLt
  have he01 : e.val=0 ∨ e.val=1 := by omega
  rcases he01 with he0|he1
  · have hr : D.antipodalResidue h t (⟨0,hh⟩,e)=⟨0,D.u_pos⟩ := by
      apply Fin.ext
      change (0*t+e.val*h)%D.u=0
      rw [he0]
      simp
    rw [hr,D.shortestDegree_zero,he0]
  · let b : D.a := ⟨h,by rw [ha]; simp⟩
    let r := D.antipodalResidue h t (⟨0,hh⟩,e)
    have hr : r=⟨h,D.a_lt _ b.property⟩ := by
      apply Fin.ext
      change (0*t+e.val*h)%D.u=h
      rw [he1]
      simp only [zero_mul,one_mul,zero_add]
      exact Nat.mod_eq_of_lt (by omega)
    have hcoord := D.coreCoordinates_internal_generator b
    have hmem := D.coordinate_mem_fiber (D.coreGeneratorPoint (D.internalVariable b))
    rw [hcoord] at hmem
    have hupp := D.shortestDegree_le ⟨h,D.a_lt _ b.property⟩ (0,0) hmem
    have hlow := D.shortestPoint_degree r
    have heps : D.epsilon r=1 := by
      rw [hr]
      simp only [epsilon]
      rw [ite_eq_right (by omega)]
    rw [heps] at hlow
    change D.shortestDegree r=e.val
    rw [hr] at hlow ⊢
    simp only [epsilon,Nat.ne_of_gt hh,ite_false,zero_add] at hupp
    rw [he1]
    omega

theorem antipodal_shortest (h t : ℕ) (hu : D.u=2*h) (hh : 0<h)
    (hc : Nat.Coprime t h) (ha : D.a={t,h,t+h}) (n : Fin h) (e : Fin 2) :
    D.shortestDegree (D.antipodalResidue h t (n,e))=if n.val=0 then e.val else n.val := by
  by_cases hn : n.val=0
  · have hn' : n=⟨0,hh⟩ := Fin.ext hn
    subst n
    rw [ite_eq_left rfl]
    exact D.antipodal_shortest_zero h t hu hh ha e
  · rw [ite_eq_right hn]
    exact D.antipodal_shortest_positive h t hu hc ha n e (by omega)

/-- Exact original word volume, from all actual residue distances. -/
theorem antipodal_wordVolume (h t : ℕ) (hu : D.u=2*h) (hh : 4 ≤ h)
    (hc : Nat.Coprime t h) (ha : D.a={t,h,t+h}) :
    D.wordVolume=h^2-h+2 := by
  have hh0 : 0<h := by omega
  unfold wordVolume
  rw [←(D.antipodalResidueEquiv h t hu hh0 hc).sum_comp D.shortestDegree]
  change 1+∑ i : Fin h × Fin 2,D.shortestDegree (D.antipodalResidue h t i)=_
  rw [Fintype.sum_prod_type]
  simp_rw [D.antipodal_shortest h t hu hh0 hc ha]
  have hsum (n : Fin h) : (∑ e : Fin 2,if n.val=0 then e.val else n.val)=
      2*n.val+(if n.val=0 then 1 else 0) := by
    by_cases hn : n.val=0 <;> simp [hn,Fin.sum_univ_two]
  simp_rw [hsum]
  rw [Finset.sum_add_distrib,←Finset.mul_sum]
  have hone : (∑ n : Fin h,if n.val=0 then 1 else 0)=1 := by
    have hn (n : Fin h) : n.val=0 ↔ n=⟨0,hh0⟩ := ⟨fun h => Fin.ext h,fun h => congrArg Fin.val h⟩
    simp_rw [hn]
    simp
  rw [hone,Fin.sum_univ_eq_sum_range (fun n : ℕ => n)]
  have hs := Finset.sum_range_id_mul_two h
  have hsub := Nat.sub_add_cancel (show 1 ≤ h by omega)
  have hh2 : h ≤ h^2 := by nlinarith only [hh]
  have hsub2 := Nat.sub_add_cancel hh2
  nlinarith only [hs,hsub,hsub2]
end NSP14.Endpoint.Data
