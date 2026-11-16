module
public import NSP14.Lex.EliahouKervaireOrdinary
public import NSP14.Endpoint.VariableIdealGraded
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open scoped Classical BigOperators
open NSP14.Homological
attribute [local instance] MvPolynomial.gradedAlgebra
namespace NSP14.Lex
variable (k : Type) [Field k] (q : ℕ)

theorem quotientGradedBetti_congr (I J : Ideal (MvPolynomial (Fin q) k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin q) k))
    (hJ : J.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin q) k))
    (he : I=J) (i : ℕ) (t : ℤ) :
    quotientGradedBetti k q I hI i t=quotientGradedBetti k q J hJ i t :=
  NSP14.Endpoint.artinGradedBetti_congr k (Fin q) I J hI hJ he i t

theorem monomialListIdeal_homogeneous (vs : List (Fin q →₀ ℕ)) :
    (monomialListIdeal k q vs).IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin q) k) := by
  unfold monomialListIdeal
  apply Ideal.homogeneous_span
  rintro _ ⟨v,_,rfl⟩
  exact ⟨v.degree,MvPolynomial.isHomogeneous_monomial (1:k) rfl⟩

theorem predecessor_homogeneous (L : Ideal (MvPolynomial (Fin q) k)) (w : Fin q →₀ ℕ) :
    (predecessorIdeal k q L w).IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin q) k) := by
  unfold predecessorIdeal
  apply Ideal.homogeneous_span
  rintro _ ⟨v,_,rfl⟩
  exact ⟨v.degree,MvPolynomial.isHomogeneous_monomial (1:k) rfl⟩

theorem predecessor_adjoin_homogeneous (L : Ideal (MvPolynomial (Fin q) k)) (w : Fin q →₀ ℕ) :
    (predecessorIdeal k q L w ⊔ Ideal.span {MvPolynomial.monomial w (1:k)}).IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin q) k) :=
  (predecessor_homogeneous k q L w).sup (by
    apply Ideal.homogeneous_span
    rintro _ rfl
    exact ⟨w.degree,MvPolynomial.isHomogeneous_monomial (1:k) rfl⟩)

noncomputable def beforeVariableIdeal (w : Fin q →₀ ℕ) : Ideal (MvPolynomial (Fin q) k) :=
  Ideal.span ((MvPolynomial.X : Fin q → MvPolynomial (Fin q) k) '' {i | i.val+1 < maxVariable q w})

theorem beforeVariableIdeal_homogeneous (w : Fin q →₀ ℕ) :
    (beforeVariableIdeal k q w).IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin q) k) := by
  unfold beforeVariableIdeal
  apply Ideal.homogeneous_span
  rintro _ ⟨i,_,rfl⟩
  exact ⟨1,MvPolynomial.isHomogeneous_X (R:=k) i⟩

theorem IsLex.predecessor_colon_eq_before {L : Ideal (MvPolynomial (Fin q) k)}
    (hL : IsLex k q L) (hproper : L ≠ ⊤) (w : Fin q →₀ ℕ) (hw : MinimalGenerator k q L w) :
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

theorem IsLex.predecessor_colon_homogeneous {L : Ideal (MvPolynomial (Fin q) k)}
    (hL : IsLex k q L) (hproper : L ≠ ⊤) (w : Fin q →₀ ℕ) (hw : MinimalGenerator k q L w) :
    ((predecessorIdeal k q L w).colon {MvPolynomial.monomial w (1:k)}).IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin q) k) := by
  rw [hL.predecessor_colon_eq_before k q hproper w hw]
  exact beforeVariableIdeal_homogeneous k q w

theorem beforeVariable_gradedBetti (w : Fin q →₀ ℕ) (hw : w ≠ 0) (i : ℕ) (t : ℤ) :
    quotientGradedBetti k q (beforeVariableIdeal k q w) (beforeVariableIdeal_homogeneous k q w) i t=
      if (i:ℤ)=t then (maxVariable q w-1).choose i else 0 := by
  obtain ⟨r,_,hm,_⟩ := maxVariable_spec q w hw
  let vs := (Finset.Iio r).toList
  have hs : {j : Fin q | j ∈ vs}={j | j.val+1 < maxVariable q w} := by
    ext j
    simp only [vs,Finset.mem_toList,Finset.mem_Iio]
    rw [hm]
    change j.val < r.val ↔ j.val+1 < r.val+1
    omega
  have he : variablesIdeal k (Fin q) vs=beforeVariableIdeal k q w := by
    unfold variablesIdeal beforeVariableIdeal
    rw [hs]
  have hlen : vs.length=r.val := by simp [vs]
  have hb := NSP14.Endpoint.variable_ideal_gradedBetti k (Fin q) vs (Finset.nodup_toList _)
    (NSP14.Endpoint.variablesIdeal_homogeneous k (Fin q) vs) i t
  change quotientGradedBetti k q (variablesIdeal k (Fin q) vs)
    (NSP14.Endpoint.variablesIdeal_homogeneous k (Fin q) vs) i t=_ at hb
  rw [quotientGradedBetti_congr k q _ _ (NSP14.Endpoint.variablesIdeal_homogeneous k (Fin q) vs)
    (beforeVariableIdeal_homogeneous k q w) he i t,hlen] at hb
  simpa only [hm,Nat.add_sub_cancel] using hb

/-- The actual graded lex adjoining step, with its actual coordinate
colon and the proved internal-degree shift. -/
theorem IsLex.predecessor_graded_step {L : Ideal (MvPolynomial (Fin q) k)}
    (hL : IsLex k q L) (hproper : L ≠ ⊤) (w : Fin q →₀ ℕ) (hw : MinimalGenerator k q L w)
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

theorem IsLex.predecessor_graded_binomial {L : Ideal (MvPolynomial (Fin q) k)}
    (hL : IsLex k q L) (hproper : L ≠ ⊤) (w : Fin q →₀ ℕ) (hw : MinimalGenerator k q L w)
    (i : ℕ) (t : ℤ) :
    quotientGradedBetti k q (predecessorIdeal k q L w ⊔ Ideal.span {MvPolynomial.monomial w (1:k)})
        (predecessor_adjoin_homogeneous k q L w) (i+1) t=
      quotientGradedBetti k q (predecessorIdeal k q L w) (predecessor_homogeneous k q L w) (i+1) t+
      (if (w.degree:ℤ)+(i:ℤ)=t then (maxVariable q w-1).choose i else 0) := by
  have hb := hL.predecessor_graded_step k q hproper w hw i t
  rw [beforeVariable_gradedBetti k q w (minimalGenerator_ne_zero q k L hproper w hw)] at hb
  have he : ((i:ℤ)=t-(w.degree:ℤ)) ↔ ((w.degree:ℤ)+(i:ℤ)=t) := by omega
  simpa only [he] using hb

theorem monomialList_graded_empty (i : ℕ) (t : ℤ) :
    quotientGradedBetti k q (monomialListIdeal k q [])
      (monomialListIdeal_homogeneous k q []) (i+1) t=0 := by
  have hb := gradedBetti_le_total k (Fin q)
    (ModuleCat.of (MvPolynomial (Fin q) k) ((MvPolynomial (Fin q) k) ⧸ monomialListIdeal k q []))
    (NSP14.Endpoint.artinGrading k (Fin q) (monomialListIdeal k q [])
      (monomialListIdeal_homogeneous k q [])) (i+1) t
  rw [monomialList_empty_betti] at hb
  exact Nat.eq_zero_of_le_zero hb

/-- Finite graded induction through the actual ordered minimal generators. -/
theorem IsLex.graded_ek_accum {L : Ideal (MvPolynomial (Fin q) k)}
    (hL : IsLex k q L) (hproper : L ≠ ⊤)
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
theorem IsLex.graded_ek {L : Ideal (MvPolynomial (Fin q) k)}
    (hL : IsLex k q L) (hproper : L ≠ ⊤)
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
