module
public import NSP14.Lex.PrefixDominance
public import NSP14.Lex.EliahouKervaire
@[expose] public section
open scoped Classical BigOperators
open NSP14.Homological
attribute [local instance] MvPolynomial.gradedAlgebra
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace NSP14.Lex

theorem reversedPrefix_le_of_head_bounds (q : ℕ) (v w : Fin (q+1) →₀ ℕ)
    (hdeg : v.degree=w.degree) (r : Fin (q+1))
    (hp : ∀ i, i < r → v i≤w i) (hw : ∀ i, r < i → w i=0) :
    ∀ t,t≤q+1 → reversedPrefix q w t≤reversedPrefix q v t := by
  intro t ht
  by_cases hcut : r.val<q+1-t
  · have hw0 : reversedPrefix q w t=0 := by
      apply Finset.sum_eq_zero
      intro j hj
      have hjt := Finset.mem_range.mp hj
      have hjn : j<q+1 := by omega
      rw [reversedCoefficient,dite_eq_left hjn]
      apply hw
      change r.val<q+1-(j+1)
      omega
    rw [hw0]
    exact Nat.zero_le _
  · have hle : (∑ j∈Finset.Ico t (q+1),reversedCoefficient q v j)≤
        ∑ j∈Finset.Ico t (q+1),reversedCoefficient q w j := by
      apply Finset.sum_le_sum
      intro j hj
      obtain ⟨htj,hjn⟩ := Finset.mem_Ico.mp hj
      rw [reversedCoefficient,reversedCoefficient,dite_eq_left hjn,dite_eq_left hjn]
      apply hp
      change q+1-(j+1) < r.val
      omega
    have hv := Finset.sum_range_add_sum_Ico (reversedCoefficient q v) ht
    have hw := Finset.sum_range_add_sum_Ico (reversedCoefficient q w) ht
    change reversedPrefix q v t+∑ j∈Finset.Ico t (q+1),reversedCoefficient q v j=reversedPrefix q v (q+1) at hv
    change reversedPrefix q w t+∑ j∈Finset.Ico t (q+1),reversedCoefficient q w j=reversedPrefix q w (q+1) at hw
    rw [reversedPrefix_total,hdeg] at hv
    rw [reversedPrefix_total] at hw
    omega

theorem IsStronglyStable.mem_of_head_bounds (k : Type) [Field k] (q : ℕ)
    (I : Ideal (MvPolynomial (Fin q) k)) (hI : IsStronglyStable k q I)
    (v w : Fin q →₀ ℕ) (hdeg : v.degree=w.degree) (r : Fin q)
    (hp : ∀ i, i < r → v i≤w i) (hw : ∀ i, r < i → w i=0)
    (hm : MvPolynomial.monomial v (1:k)∈I) : MvPolynomial.monomial w (1:k)∈I := by
  cases q with
  | zero => exact Fin.elim0 r
  | succ q => exact hI.mem_of_tail_le k q I v w hdeg (reversedPrefix_le_of_head_bounds q v w hdeg r hp hw) hm
end NSP14.Lex

namespace NSP14.Lex
variable (k : Type) [Field k] (q : ℕ)

theorem IsStronglyStable.raise {L : Ideal (MvPolynomial (Fin q) k)} (hL : IsStronglyStable k q L)
    (v : Fin q →₀ ℕ) (hv : MvPolynomial.monomial v (1:k)∈L)
    (i j : Fin q) (hj : 0<v j) (hij : i<j) :
    MvPolynomial.monomial (raisedExponent q v i j) (1:k)∈L := hL.2 v hv i j hj hij

theorem IsStronglyStable.predecessor_divisor {L : Ideal (MvPolynomial (Fin q) k)}
    (hL : IsStronglyStable k q L) (w : Fin q →₀ ℕ) (hw : MinimalGenerator k q L w)
    (r : Fin q) (hr : 0 < w r) (hmax : ∀ i, r < i → w i=0)
    (z v : Fin q →₀ ℕ) (hv : MvPolynomial.monomial v (1:k) ∈ L)
    (hpre : precedes q v w) (hdiv : v ≤ z+w) :
    ∃ i : Fin q, i < r ∧ 0 < z i := by
  by_contra! hn
  have hp : ∀ i, i < r → v i ≤ w i := by
    intro i hi
    have hz := hn i hi
    have hc := hdiv i
    simp only [Finsupp.add_apply] at hc
    omega
  rcases hpre with hdeg|⟨hdeg,hlex⟩
  · let a := w-Finsupp.single r 1
    have hsingle : Finsupp.single r 1 ≤ w := by
      intro i
      by_cases hi : r=i
      · subst i; simpa using (Nat.succ_le_of_lt hr)
      · simp only [Finsupp.single_eq_of_ne' hi]; exact Nat.zero_le _
    have haadd : a+Finsupp.single r 1=w := tsub_add_cancel_of_le hsingle
    have had : a.degree+1=w.degree := by
      have h := congrArg Finsupp.degree haadd
      simpa only [map_add,Finsupp.degree_single] using h
    let v' := v+Finsupp.single r (a.degree-v.degree)
    have hvl : v.degree ≤ a.degree := by omega
    have hvd : v'.degree=a.degree := by
      dsimp only [v']
      rw [map_add,Finsupp.degree_single]
      omega
    have hhead : ∀ i, i < r → v' i≤a i := by
      intro i hi
      have hri : r≠i := (ne_of_lt hi).symm
      simpa only [v',a,Finsupp.add_apply,Finsupp.tsub_apply,
        Finsupp.single_eq_of_ne' hri,add_zero,Nat.sub_zero] using hp i hi
    have hamax : ∀ i, r < i → a i=0 := by
      intro i hi
      simp only [a,Finsupp.tsub_apply,hmax i hi,Nat.zero_sub]
    have hvmem : MvPolynomial.monomial v' (1:k) ∈ L :=
      monomial_mem_of_le k q L v v' hv (by intro i; simp only [v',Finsupp.add_apply]; omega)
    have hamem := hL.mem_of_head_bounds k q L v' a hvd r hhead hamax hvmem
    have hal : a ≤ w := by intro i; exact Nat.sub_le _ _
    have hae := hw.2 a hal hamem
    have hd := congrArg Finsupp.degree hae
    omega
  · have hle := lex_le_of_prefix q v w r hdeg hp hmax
    exact (not_lt_of_ge hle hlex)

theorem IsStronglyStable.predecessor_colon_monomial {L : Ideal (MvPolynomial (Fin q) k)}
    (hL : IsStronglyStable k q L) (w : Fin q →₀ ℕ) (hw : MinimalGenerator k q L w)
    (r : Fin q) (hr : 0 < w r) (hmax : ∀ i, r < i → w i=0)
    (z : Fin q →₀ ℕ) :
    MvPolynomial.monomial z (1:k) ∈
      (predecessorIdeal k q L w).colon {MvPolynomial.monomial w (1:k)} ↔
      ∃ i : Fin q, i < r ∧ 0 < z i := by
  rw [Submodule.mem_colon_singleton]
  change MvPolynomial.monomial z (1:k)*MvPolynomial.monomial w (1:k) ∈ _ ↔ _
  rw [MvPolynomial.monomial_mul_monomial,one_mul]
  change MvPolynomial.monomial (z+w) (1:k) ∈
    Ideal.span ((fun v => MvPolynomial.monomial v (1:k)) ''
      {v | MvPolynomial.monomial v (1:k) ∈ L ∧ precedes q v w}) ↔ _
  rw [monomial_mem_span_iff]
  constructor
  · rintro ⟨v,⟨hv,hpre⟩,hdiv⟩
    exact hL.predecessor_divisor k q w hw r hr hmax z v hv hpre hdiv
  · rintro ⟨i,hi,hzi⟩
    refine ⟨raisedExponent q w i r,⟨hL.raise k q w hw.1 i r hr hi,
      Or.inr ⟨raisedExponent_degree q w i r hr,raisedExponent_lex q w i r hi⟩⟩,?_⟩
    intro j
    by_cases hij : i=j
    · subst j
      have hri : r ≠ i := (ne_of_lt hi).symm
      simp only [raisedExponent,Finsupp.add_apply,Finsupp.tsub_apply,
        Finsupp.single_eq_of_ne' hri,Finsupp.single_eq_same,Nat.sub_zero]
      omega
    · simp only [raisedExponent,Finsupp.add_apply,Finsupp.tsub_apply,
        Finsupp.single_eq_of_ne' hij,add_zero]
      omega

/-- The actual colon at the next ordered minimal generator is the ideal of the
variables preceding its largest variable. This constructs no Tor premise. -/
theorem IsStronglyStable.predecessor_colon {L : Ideal (MvPolynomial (Fin q) k)}
    (hL : IsStronglyStable k q L) (w : Fin q →₀ ℕ) (hw : MinimalGenerator k q L w)
    (r : Fin q) (hr : 0 < w r) (hmax : ∀ i, r < i → w i=0) :
    (predecessorIdeal k q L w).colon {MvPolynomial.monomial w (1:k)} =
      Ideal.span (MvPolynomial.X '' {i : Fin q | i < r}) := by
  apply le_antisymm
  · intro f hf
    apply MvPolynomial.mem_ideal_span_X_image.mpr
    intro z hz
    have hf' : f*MvPolynomial.monomial w (1:k) ∈ predecessorIdeal k q L w :=
      Submodule.mem_colon_singleton.mp hf
    have hz' : z+w ∈ (f*MvPolynomial.monomial w (1:k)).support := by
      rw [MvPolynomial.mem_support_iff,MvPolynomial.coeff_mul_monomial,mul_one]
      exact MvPolynomial.mem_support_iff.mp hz
    obtain ⟨v,⟨hv,hpre⟩,hdiv⟩ := MvPolynomial.mem_ideal_span_monomial_image.mp hf' (z+w) hz'
    obtain ⟨i,hi,hzi⟩ := hL.predecessor_divisor k q w hw r hr hmax z v hv hpre hdiv
    exact ⟨i,hi,ne_of_gt hzi⟩
  · apply Ideal.span_le.mpr
    rintro _ ⟨i,hi,rfl⟩
    change MvPolynomial.monomial (Finsupp.single i 1) (1:k) ∈
      (predecessorIdeal k q L w).colon {MvPolynomial.monomial w (1:k)}
    apply (hL.predecessor_colon_monomial k q w hw r hr hmax _).mpr
    exact ⟨i,hi,by simp⟩

theorem IsStronglyStable.predecessor_factor_colon {L : Ideal (MvPolynomial (Fin q) k)}
    (hL : IsStronglyStable k q L) (w : Fin q →₀ ℕ) (hw : MinimalGenerator k q L w)
    (r : Fin q) (hr : 0 < w r) (hmax : ∀ i, r < i → w i=0) :
    (predecessorIdeal k q L w).colon {MvPolynomial.monomial w (1:k)} ≤
      (predecessorIdeal k q L w).colon {MvPolynomial.monomial (w-Finsupp.single r 1) (1:k)} := by
  rw [hL.predecessor_colon k q w hw r hr hmax]
  apply Ideal.span_le.mpr
  rintro _ ⟨i,hi,rfl⟩
  apply Submodule.mem_colon_singleton.mpr
  change MvPolynomial.X i * MvPolynomial.monomial (w-Finsupp.single r 1) (1:k) ∈ predecessorIdeal k q L w
  rw [MvPolynomial.X,MvPolynomial.monomial_mul_monomial,one_mul,add_comm]
  exact Ideal.subset_span ⟨raisedExponent q w i r,
    ⟨hL.raise k q w hw.1 i r hr hi,
      Or.inr ⟨raisedExponent_degree q w i r hr,raisedExponent_lex q w i r hi⟩⟩,rfl⟩

theorem IsStronglyStable.predecessor_colon_eq_before {L : Ideal (MvPolynomial (Fin q) k)}
    (hL : IsStronglyStable k q L) (hproper : L ≠ ⊤) (w : Fin q →₀ ℕ) (hw : MinimalGenerator k q L w) :
    (predecessorIdeal k q L w).colon {MvPolynomial.monomial w (1:k)}=beforeVariableIdeal k q w := by
  obtain ⟨r,hr,hm,hmax⟩ := maxVariable_spec q w (minimalGenerator_ne_zero q k L hproper w hw)
  rw [hL.predecessor_colon k q w hw r hr hmax]
  have hs : {j : Fin q | j < r}={j | j.val+1 < maxVariable q w} := by
    ext j
    rw [hm]
    change j.val < r.val ↔ j.val+1 < r.val+1
    omega
  unfold beforeVariableIdeal
  rw [hs]

theorem IsStronglyStable.predecessor_colon_homogeneous {L : Ideal (MvPolynomial (Fin q) k)}
    (hL : IsStronglyStable k q L) (hproper : L ≠ ⊤) (w : Fin q →₀ ℕ) (hw : MinimalGenerator k q L w) :
    ((predecessorIdeal k q L w).colon {MvPolynomial.monomial w (1:k)}).IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin q) k) := by
  rw [hL.predecessor_colon_eq_before k q hproper w hw]
  exact beforeVariableIdeal_homogeneous k q w

theorem IsStronglyStable.predecessor_graded_step {L : Ideal (MvPolynomial (Fin q) k)}
    (hL : IsStronglyStable k q L) (hproper : L ≠ ⊤) (w : Fin q →₀ ℕ) (hw : MinimalGenerator k q L w)
    (i : ℕ) (t : ℤ) :
    quotientGradedBetti k q (predecessorIdeal k q L w ⊔ Ideal.span {MvPolynomial.monomial w (1:k)})
        (predecessor_adjoin_homogeneous k q L w) (i+1) t=
      quotientGradedBetti k q (predecessorIdeal k q L w) (predecessor_homogeneous k q L w) (i+1) t+
      quotientGradedBetti k q (beforeVariableIdeal k q w) (beforeVariableIdeal_homogeneous k q w) i (t-(w.degree:ℤ)) := by
  obtain ⟨r,hr,_,hmax⟩ := maxVariable_spec q w (minimalGenerator_ne_zero q k L hproper w hw)
  let J := predecessorIdeal k q L w
  let g := MvPolynomial.monomial w (1:k)
  let h := MvPolynomial.monomial (w-Finsupp.single r 1) (1:k)
  have hJ := predecessor_homogeneous k q L w
  have hK := predecessor_adjoin_homogeneous k q L w
  have hC := hL.predecessor_colon_homogeneous k q hproper w hw
  have hb := NSP14.Endpoint.artin_adjoin_gradedBetti k (Fin q) J g h r hJ hK hC w.degree
    (MvPolynomial.isHomogeneous_monomial (1:k) rfl) (exponent_remove_max_factor k q w r hr)
    (hL.predecessor_factor_colon k q w hw r hr hmax) i t
  change quotientGradedBetti k q (J ⊔ Ideal.span {g}) hK (i+1) t=
    quotientGradedBetti k q J hJ (i+1) t+quotientGradedBetti k q (J.colon {g}) hC i (t-(w.degree:ℤ)) at hb
  rw [quotientGradedBetti_congr k q _ _ hC (beforeVariableIdeal_homogeneous k q w)
    (hL.predecessor_colon_eq_before k q hproper w hw) i (t-(w.degree:ℤ))] at hb
  exact hb

theorem IsStronglyStable.predecessor_graded_binomial {L : Ideal (MvPolynomial (Fin q) k)}
    (hL : IsStronglyStable k q L) (hproper : L ≠ ⊤) (w : Fin q →₀ ℕ) (hw : MinimalGenerator k q L w)
    (i : ℕ) (t : ℤ) :
    quotientGradedBetti k q (predecessorIdeal k q L w ⊔ Ideal.span {MvPolynomial.monomial w (1:k)})
        (predecessor_adjoin_homogeneous k q L w) (i+1) t=
      quotientGradedBetti k q (predecessorIdeal k q L w) (predecessor_homogeneous k q L w) (i+1) t+
      (if (w.degree:ℤ)+(i:ℤ)=t then (maxVariable q w-1).choose i else 0) := by
  have hb := hL.predecessor_graded_step k q hproper w hw i t
  rw [beforeVariable_gradedBetti k q w (minimalGenerator_ne_zero q k L hproper w hw)] at hb
  have he : ((i:ℤ)=t-(w.degree:ℤ)) ↔ ((w.degree:ℤ)+(i:ℤ)=t) := by omega
  simpa only [he] using hb

theorem IsStronglyStable.graded_ek_accum {L : Ideal (MvPolynomial (Fin q) k)}
    (hL : IsStronglyStable k q L) (hproper : L ≠ ⊤)
    (hHom : L.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin q) k))
    (pre rest : List (Fin q →₀ ℕ)) (hsplit : generatorList q k L=pre++rest) (i : ℕ) (t : ℤ) :
    quotientGradedBetti k q L hHom (i+1) t=
      quotientGradedBetti k q (monomialListIdeal k q pre) (monomialListIdeal_homogeneous k q pre) (i+1) t+
      (rest.map (fun v => if (v.degree:ℤ)+(i:ℤ)=t then (maxVariable q v-1).choose i else 0)).sum := by
  induction rest generalizing pre with
  | nil =>
    have he : generatorList q k L=pre := by simpa only [List.append_nil] using hsplit
    have hp : monomialListIdeal k q pre=L := by
      rw [←he]
      exact generatorListIdeal_eq k q L hL.1
    rw [quotientGradedBetti_congr k q _ _ (monomialListIdeal_homogeneous k q pre) hHom hp]
    simp
  | cons w rest ih =>
    have hm : MinimalGenerator k q L w := by
      apply (generatorList_mem k q L w).mp
      rw [hsplit]
      exact List.mem_append.mpr (Or.inr List.mem_cons_self)
    have hsplit' : generatorList q k L=(pre++[w])++rest := by
      simpa only [List.append_assoc,List.singleton_append] using hsplit
    have hh := ih (pre++[w]) hsplit'
    have hs := hL.predecessor_graded_binomial k q hproper w hm i t
    have hp := predecessorIdeal_of_split k q L pre rest w hsplit
    have hsnoc : predecessorIdeal k q L w ⊔ Ideal.span {MvPolynomial.monomial w (1:k)}=
        monomialListIdeal k q (pre++[w]) := by
      rw [monomialListIdeal_append,monomialListIdeal_singleton,hp]
    rw [quotientGradedBetti_congr k q _ _ (predecessor_adjoin_homogeneous k q L w)
      (monomialListIdeal_homogeneous k q (pre++[w])) hsnoc,
      quotientGradedBetti_congr k q _ _ (predecessor_homogeneous k q L w)
      (monomialListIdeal_homogeneous k q pre) hp] at hs
    rw [hs] at hh
    simpa only [List.map_cons,List.sum_cons,add_assoc] using hh

/-- Actual graded quotient EK over arbitrary fields, in every positive row and every internal degree. -/
theorem IsStronglyStable.graded_ek {L : Ideal (MvPolynomial (Fin q) k)}
    (hL : IsStronglyStable k q L) (hproper : L ≠ ⊤)
    (hHom : L.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin q) k))
    (g : Finset (Fin q →₀ ℕ)) (hg : ∀ v,v ∈ g ↔ MinimalGenerator k q L v)
    (i : ℕ) (hi : 1 ≤ i) (t : ℤ) :
    quotientGradedBetti k q L hHom i t=
      ∑ v ∈ g, if (v.degree:ℤ)+(i:ℤ)-1=t then (maxVariable q v-1).choose (i-1) else 0 := by
  obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0)
  have hh := hL.graded_ek_accum k q hproper hHom [] (generatorList q k L) rfl j t
  rw [monomialList_graded_empty,zero_add] at hh
  have hn : (generatorList q k L).Nodup := Finset.sort_nodup _ _
  rw [list_sum_map_toFinset q _ hn,generatorList_toFinset] at hh
  have he : minimalGeneratorFinset k q L=g := by
    ext v
    rw [mem_minimalGeneratorFinset,hg]
  rw [he] at hh
  simpa only [Nat.succ_eq_add_one,Nat.add_sub_cancel,Nat.cast_add,Nat.cast_one,
    ←add_assoc,add_sub_cancel_right] using hh

end NSP14.Lex
