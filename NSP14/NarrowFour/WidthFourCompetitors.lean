module
public import NSP14.NarrowFour.WidthFourCore
@[expose] public section
set_option backward.isDefEq.respectTransparency false
namespace NSP14.NarrowFour.WidthFour

def residue (m n j : ℕ) : Fin 4 :=
  ⟨((n:ℤ)-(j:ℤ)*m)%4 |>.toNat,by
    have hl := Int.emod_nonneg ((n:ℤ)-(j:ℤ)*m) (by omega : (4:ℤ)≠0)
    have hu := Int.emod_lt_of_pos ((n:ℤ)-(j:ℤ)*m) (by omega : (0:ℤ)<4)
    omega⟩

def kappa (m n j : ℕ) : ℤ := ((j:ℤ)*m+(residue m n j).val-n)/4

def lambda (r : Fin 4) : ℕ := match r.val with | 0 => 0 | 2 => 2 | _ => 1

theorem residue_cast (m n j : ℕ) : ((residue m n j).val:ℤ)=((n:ℤ)-(j:ℤ)*m)%4 := by
  dsimp [residue]
  have h := Int.emod_nonneg ((n:ℤ)-(j:ℤ)*m) (by omega : (4:ℤ)≠0)
  omega

theorem kappa_eq (m n j : ℕ) : 4*kappa m n j=(j:ℤ)*m+(residue m n j).val-n := by
  have hr := residue_cast m n j
  have he := Int.emod_add_mul_ediv ((n:ℤ)-(j:ℤ)*m) 4
  unfold kappa
  omega

theorem kappa_ceil (m n j : ℕ) : kappa m n j=-(((n:ℤ)-(j:ℤ)*m)/4) := by
  have hk := kappa_eq m n j
  have hr := residue_cast m n j
  have he := Int.emod_add_mul_ediv ((n:ℤ)-(j:ℤ)*m) 4
  omega

theorem lambda_bound (r : Fin 4) : 4*(lambda r:ℤ)-r.val ≤ 6 := by
  fin_cases r <;> norm_num [lambda]

def delta (m : ℕ) (i : Fin 5) (j : ℕ) : ℤ :=
  (lambda (residue m (anchorN i) j):ℤ)-anchorC i-kappa m (anchorN i) j-j

theorem delta_identity (m : ℕ) (i : Fin 5) (j : ℕ) :
    4*delta m i j=(4*(lambda (residue m (anchorN i) j):ℤ)-(residue m (anchorN i) j).val)-
      (4*(anchorC i:ℤ)-anchorN i)-(j:ℤ)*((m:ℤ)+4) := by
  have hk := kappa_eq m (anchorN i) j
  unfold delta
  nlinarith only [hk]

theorem delta_neg (m : ℕ) (hm : 6 ≤ m) (i : Fin 5) (j : ℕ) (hj : 1 ≤ j) : delta m i j<0 := by
  have hi := delta_identity m i j
  have hlam := lambda_bound (residue m (anchorN i) j)
  have hn : (anchorN i:ℤ) ≤ 4*(anchorC i:ℤ) := by exact_mod_cast anchor_bound i
  have hmz : (6:ℤ) ≤ m := by exact_mod_cast hm
  have hjz : (1:ℤ) ≤ j := by exact_mod_cast hj
  have hp := mul_nonneg (show (0:ℤ) ≤ (j:ℤ)-1 by omega) (show (0:ℤ) ≤ (m:ℤ)+4 by omega)
  nlinarith only [hi,hlam,hn,hmz,hp]

theorem kappa_monotone (m n : ℕ) (hm : 6 ≤ m) : Monotone (kappa m n) := by
  apply monotone_nat_of_le_succ
  intro j
  have h0 := kappa_eq m n j
  have h1 := kappa_eq m n (j+1)
  have hr0 := (residue m n j).isLt
  have hr1 := (residue m n (j+1)).isLt
  push_cast at h1
  ring_nf at h0 h1
  simp only [Nat.add_comm 1 j] at h1
  have hmz : (6:ℤ) ≤ m := by exact_mod_cast hm
  omega

/-- Both degree and offset coordinates, before nonnegativity is discarded. -/
theorem free_coordinates (m : ℕ) (i : Fin 5) (j : ℕ) (r : Fin 4) (L K L' K' : ℤ) :
    ((r.val:ℤ)+4*K'=(anchorN i:ℤ)+4*K-(j:ℤ)*m ∧
      L'+K'+lambda r=L+K+anchorC i+j) ↔
    (r=residue m (anchorN i) j ∧ K'=K-kappa m (anchorN i) j ∧ L'=L-delta m i j) := by
  have hk := kappa_eq m (anchorN i) j
  constructor
  · intro h
    have he := Int.emod_add_mul_ediv ((anchorN i:ℤ)-(j:ℤ)*m) 4
    have hr := residue_cast m (anchorN i) j
    have hrl := r.isLt
    have hrr := (residue m (anchorN i) j).isLt
    have hval : r.val=(residue m (anchorN i) j).val := by omega
    have hre : r=residue m (anchorN i) j := Fin.ext hval
    subst r
    unfold delta
    exact ⟨rfl,by omega,by omega⟩
  · rintro ⟨rfl,hK,hL⟩
    unfold delta at hL
    exact ⟨by omega,by omega⟩

/-- All j, both coordinate constraints: only K remains once delta<0 is proved. -/
theorem free_exists_iff (m : ℕ) (hm : 6 ≤ m) (i : Fin 5) (j : ℕ) (hj : 1 ≤ j)
    (L K : ℤ) (hL : 0 ≤ L) :
    (∃ (r : Fin 4) (L' K' : ℤ),0 ≤ L' ∧ 0 ≤ K' ∧
      (r.val:ℤ)+4*K'=(anchorN i:ℤ)+4*K-(j:ℤ)*m ∧
      L'+K'+lambda r=L+K+anchorC i+j) ↔ kappa m (anchorN i) j ≤ K := by
  constructor
  · rintro ⟨r,L',K',_,hK,h⟩
    have hc := (free_coordinates m i j r L K L' K').mp h
    omega
  · intro hK
    have hd := delta_neg m hm i j hj
    refine ⟨residue m (anchorN i) j,L-delta m i j,K-kappa m (anchorN i) j,by omega,by omega,?_⟩
    exact (free_coordinates m i j _ L K _ _).mpr ⟨rfl,rfl,rfl⟩

def theta (m n : ℕ) : ℕ := (kappa m n 1).toNat

theorem anchorN_le_six (i : Fin 5) : anchorN i ≤ 6 := by fin_cases i <;> decide

theorem kappa_one_nonneg (m : ℕ) (hm : 6 ≤ m) (i : Fin 5) : 0 ≤ kappa m (anchorN i) 1 := by
  have hk := kappa_eq m (anchorN i) 1
  have hn := anchorN_le_six i
  norm_num only [Nat.cast_one,one_mul] at hk
  omega

theorem theta_cast (m : ℕ) (hm : 6 ≤ m) (i : Fin 5) :
    (theta m (anchorN i):ℤ)=kappa m (anchorN i) 1 := by
  exact Int.toNat_of_nonneg (kappa_one_nonneg m hm i)

theorem all_j_threshold (m : ℕ) (hm : 6 ≤ m) (i : Fin 5) (K : ℕ) :
    (∃ j : ℕ,1 ≤ j ∧ kappa m (anchorN i) j ≤ K) ↔ theta m (anchorN i) ≤ K := by
  have ht := theta_cast m hm i
  constructor
  · rintro ⟨j,hj,hK⟩
    have hmono := kappa_monotone m (anchorN i) hm hj
    omega
  · intro hK
    exact ⟨1,le_rfl,by omega⟩


def freeColumn (r : Fin 4) (L K : ℕ) : Column :=
  ⟨⟨r.val,by have := r.isLt;omega⟩,L,K,by
    intro h
    have he := congrArg Fin.val h
    have hr := r.isLt
    dsimp at he
    omega⟩

theorem freeColumn_degree (r : Fin 4) (L K : ℕ) :
    (freeColumn r L K).degree=L+K+lambda r := by
  fin_cases r <;> rfl

theorem freeColumn_offset (r : Fin 4) (L K : ℕ) :
    (freeColumn r L K).offset=r.val+4*K := by fin_cases r <;> rfl

theorem anchorC_free (i : Fin 5) (hi : i.val<4) : anchorC i=lambda ⟨i.val,hi⟩ := by
  have hc : i.val=0 ∨ i.val=1 ∨ i.val=2 ∨ i.val=3 := by omega
  rcases hc with h|h|h|h <;> simp [anchorC,lambda,h]
theorem anchorN_free (i : Fin 5) (hi : i.val<4) : anchorN i=i.val := by
  have hc : i.val=0 ∨ i.val=1 ∨ i.val=2 ∨ i.val=3 := by omega
  rcases hc with h|h|h|h <;> simp [anchorN,h]

theorem column_slack (p : Column) : p.offset ≤ 4*p.degree := by
  have hn := anchor_bound p.anchor
  dsimp [Column.degree,Column.offset]
  omega

/-- A longer restricted column cannot meet a nonnegative original column. In particular
its stricter K threshold is never used to discard a genuine competitor. -/
theorem restricted_long_impossible (m : ℕ) (hm : 6 ≤ m) (p q : Column) (j : ℕ) (hj : 1 ≤ j)
    (hq : q.anchor=4) (hd : q.degree=p.degree+j) (ho : p.offset=q.offset+j*m) : False := by
  have hL := q.restricted hq
  have hqeq : q.offset+2=4*q.degree := by
    simp only [Column.offset,Column.degree,hq,hL,zero_add]
    norm_num [anchorN,anchorC]
    ring
  have hp := column_slack p
  have hmul := Nat.mul_le_mul_left j hm
  nlinarith only [hqeq,hd,ho,hp,hj,hmul]

variable (D : Endpoint.Data)

theorem columnPoint_degree (hu : D.u=4) (ha : D.a={1,3}) (p : Column) :
    D.coreDegree (columnPoint D ha p)=p.degree := congrArg Prod.fst (columnPoint_coe D hu ha p)
theorem columnPoint_offset (hu : D.u=4) (ha : D.a={1,3}) (p : Column) :
    D.coreOffset (columnPoint D ha p)=p.offset := congrArg Prod.snd (columnPoint_coe D hu ha p)

/-- Exact all-j characterization on actual core points and actual numerical order. -/
theorem column_dead_iff (hm : 6 ≤ D.m) (hd : D.d=1) (hu : D.u=4) (ha : D.a={1,3}) (p : Column) :
    D.coreDegree (columnPoint D ha p)<D.source.order (D.coreValue (columnPoint D ha p)).val ↔
      theta D.m (anchorN p.anchor) ≤ p.K := by
  rw [D.core_dead_iff_competitor]
  constructor
  · rintro ⟨j,hj,q,hdeg,hoff⟩
    obtain ⟨c,rfl⟩ := columnPoint_surjective D hu ha q
    rw [columnPoint_degree D hu ha,columnPoint_degree D hu ha,hd,mul_one] at hdeg
    rw [columnPoint_offset D hu ha,columnPoint_offset D hu ha] at hoff
    have hfree : c.anchor.val<4 := by
      have hc := c.anchor.isLt
      by_contra hn
      have he : c.anchor=4 := Fin.ext (by omega)
      exact restricted_long_impossible D.m hm p c j hj he hdeg hoff
    let r : Fin 4 := ⟨c.anchor.val,hfree⟩
    have hcC : anchorC c.anchor=lambda r := anchorC_free c.anchor hfree
    have hcN : anchorN c.anchor=r.val := anchorN_free c.anchor hfree
    change c.L+c.K+anchorC c.anchor=p.L+p.K+anchorC p.anchor+j at hdeg
    change anchorN p.anchor+4*p.K=anchorN c.anchor+4*c.K+j*D.m at hoff
    rw [hcC] at hdeg
    rw [hcN] at hoff
    have hdegZ : (c.L:ℤ)+c.K+lambda r=(p.L:ℤ)+p.K+anchorC p.anchor+j := by exact_mod_cast hdeg
    have hoffZ : (r.val:ℤ)+4*c.K=(anchorN p.anchor:ℤ)+4*p.K-(j:ℤ)*D.m := by
      have h : (anchorN p.anchor:ℤ)+4*p.K=(r.val:ℤ)+4*c.K+(j:ℤ)*D.m := by exact_mod_cast hoff
      omega
    have hc := (free_coordinates D.m p.anchor j r (p.L:ℤ) (p.K:ℤ) (c.L:ℤ) (c.K:ℤ)).mp ⟨hoffZ,hdegZ⟩
    apply (all_j_threshold D.m hm p.anchor p.K).mp
    exact ⟨j,hj,by omega⟩
  · intro hK
    have htheta := theta_cast D.m hm p.anchor
    have hk : kappa D.m (anchorN p.anchor) 1 ≤ (p.K:ℤ) := by omega
    obtain ⟨r,L,K,hL,hK',hoff,hdeg⟩ := (free_exists_iff D.m hm p.anchor 1 (by omega)
      (p.L:ℤ) (p.K:ℤ) (by positivity)).mpr hk
    let q := freeColumn r L.toNat K.toNat
    have hLc : (L.toNat:ℤ)=L := Int.toNat_of_nonneg hL
    have hKc : (K.toNat:ℤ)=K := Int.toNat_of_nonneg hK'
    have hdegq : q.degree=p.degree+1 := by
      have he : (q.degree:ℤ)=(p.degree:ℤ)+1 := by
        rw [freeColumn_degree]
        push_cast
        rw [hLc,hKc]
        exact hdeg
      exact_mod_cast he
    have hoffq : p.offset=q.offset+1*D.m := by
      have he : (p.offset:ℤ)=(q.offset:ℤ)+1*(D.m:ℤ) := by
        rw [freeColumn_offset]
        dsimp [Column.offset]
        rw [hKc]
        norm_num only [Nat.cast_one,one_mul] at hoff
        omega
      exact_mod_cast he
    refine ⟨1,by omega,columnPoint D ha q,?_,?_⟩
    · rw [columnPoint_degree D hu ha,columnPoint_degree D hu ha,hd,mul_one]
      exact hdegq
    · rw [columnPoint_offset D hu ha,columnPoint_offset D hu ha]
      exact hoffq

theorem column_zero_iff (k : Type) [Field k] (hm : 6 ≤ D.m) (hd : D.d=1) (hu : D.u=4)
    (ha : D.a={1,3}) (p : Column) :
    D.coreToG k (D.coreMonomial k (columnPoint D ha p))=0 ↔ theta D.m (anchorN p.anchor) ≤ p.K := by
  rw [D.coreToG_monomial_zero_iff,column_dead_iff D hm hd hu ha]


def LiveColumn (m : ℕ) := {p : Column // p.K<theta m (anchorN p.anchor)}

noncomputable def liveImage (k : Type) [Field k] (ha : D.a={1,3}) (p : LiveColumn D.m) :
    D.source.TangentAlgebra k := D.coreToG k (D.coreMonomial k (columnPoint D ha p.val))

theorem live_degree (hm : 6 ≤ D.m) (hd : D.d=1) (hu : D.u=4) (ha : D.a={1,3}) (p : LiveColumn D.m) :
    D.coreDegree (columnPoint D ha p.val)=D.source.order (D.coreValue (columnPoint D ha p.val)).val := by
  have hl := D.coreDegree_le_order (columnPoint D ha p.val)
  have hn : ¬D.coreDegree (columnPoint D ha p.val)<D.source.order (D.coreValue (columnPoint D ha p.val)).val := by
    rw [column_dead_iff D hm hd hu ha]
    exact not_le_of_gt p.property
  omega

/-- Infinite-dimensional G causes no finrank shortcut: explicit coefficient duals
prove independence of every finite linear combination of nonforbidden columns. -/
theorem live_images_independent (k : Type) [Field k] (hm : 6 ≤ D.m) (hd : D.d=1)
    (hu : D.u=4) (ha : D.a={1,3}) : LinearIndependent k (liveImage D k ha) := by
  let f (p : LiveColumn D.m) : Module.Dual k (D.source.TangentAlgebra k) := {
    toFun a := D.source.tangentCoordinates k a (D.coreValue (columnPoint D ha p.val))
    map_add' a b := by simp only [map_add,Finsupp.add_apply]
    map_smul' c a := by simp only [map_smul,Finsupp.smul_apply,RingHom.id_apply] }
  apply LinearIndependent.of_pairwise_dual_eq_zero_one (liveImage D k ha) f
  · intro p q hpq
    change D.source.tangentCoordinates k (D.coreToG k (D.coreMonomial k (columnPoint D ha q.val)))
      (D.coreValue (columnPoint D ha p.val))=0
    rw [D.coreToG_live_coefficient k _ (live_degree D hm hd hu ha p)]
    have hne : columnPoint D ha q.val≠columnPoint D ha p.val := by
      intro h
      apply hpq
      exact (Subtype.ext (columnPoint_injective D hu ha h)).symm
    simp only [Endpoint.Data.coreMonomial,AddMonoidAlgebra.coeff_single,Finsupp.single_apply,hne,ite_false]
  · intro p
    change D.source.tangentCoordinates k (D.coreToG k (D.coreMonomial k (columnPoint D ha p.val)))
      (D.coreValue (columnPoint D ha p.val))=1
    rw [D.coreToG_live_coefficient k _ (live_degree D hm hd hu ha p)]
    simp only [Endpoint.Data.coreMonomial,AddMonoidAlgebra.coeff_single,Finsupp.single_apply,ite_true]
end NSP14.NarrowFour.WidthFour
