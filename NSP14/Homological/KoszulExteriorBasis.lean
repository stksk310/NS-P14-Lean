module
public import NSP14.Homological.KoszulSlotArrow
public import Mathlib.LinearAlgebra.ExteriorPower.Basis
public import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
@[expose] public section
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false
namespace NSP14.Homological
variable {σ : Type}
noncomputable def koszulSlotList : ∀ (xs : List σ) (j : ℕ), KoszulSlot xs.length j → List σ
  | [],0,_ => []
  | [],_+1,s => s.elim
  | _x::xs,0,s => koszulSlotList xs 0 s
  | x::xs,j+1,.inl s => x::koszulSlotList xs j s
  | _x::xs,j+1,.inr s => koszulSlotList xs (j+1) s

theorem koszulSlotList_length (xs : List σ) (j : ℕ) (s : KoszulSlot xs.length j) :
    (koszulSlotList xs j s).length=j := by
  induction xs generalizing j with
  | nil => cases j with
    | zero => rfl
    | succ j => exact s.elim
  | cons x xs ih =>
    cases j with
    | zero => exact ih 0 s
    | succ j => cases s with
      | inl s => simpa only [koszulSlotList,List.length_cons] using congrArg Nat.succ (ih j s)
      | inr s => exact ih (j+1) s

theorem koszulSlotList_toFinset (xs : List σ) (j : ℕ) (s : KoszulSlot xs.length j) :
    (koszulSlotList xs j s).toFinset=koszulSlotWedge xs j s := by
  induction xs generalizing j with
  | nil => cases j with
    | zero => rfl
    | succ j => exact s.elim
  | cons x xs ih =>
    cases j with
    | zero => exact ih 0 s
    | succ j => cases s with
      | inl s => simpa only [koszulSlotList,List.toFinset_cons,koszulSlotWedge] using congrArg (insert x) (ih j s)
      | inr s => exact ih (j+1) s

theorem koszulSlotList_nodup (xs : List σ) (hxs : xs.Nodup) (j : ℕ) (s : KoszulSlot xs.length j) :
    (koszulSlotList xs j s).Nodup := by
  induction xs generalizing j with
  | nil => cases j with
    | zero => exact List.nodup_nil
    | succ j => exact s.elim
  | cons x xs ih =>
    have hx := List.nodup_cons.mp hxs
    cases j with
    | zero => exact ih hx.2 0 s
    | succ j => cases s with
      | inl s =>
        apply List.nodup_cons.mpr
        refine ⟨?_,ih hx.2 j s⟩
        intro hs
        have hs' : x∈koszulSlotWedge xs j s := by
          rw [← koszulSlotList_toFinset]
          exact List.mem_toFinset.mpr hs
        exact hx.1 (koszulSlotWedge_mem xs j s x hs')
      | inr s => exact ih hx.2 (j+1) s

noncomputable def koszulSlotTuple (xs : List σ) (hxs : xs.Nodup) (j : ℕ)
    (s : KoszulSlot xs.length j) : Fin j ↪ σ where
  toFun i := (koszulSlotList xs j s).get (Fin.cast (koszulSlotList_length xs j s).symm i)
  inj' a b hab := by
    have he := (koszulSlotList_nodup xs hxs j s).injective_get hab
    exact Fin.cast_injective _ he

theorem koszulSlotTuple_range (xs : List σ) (hxs : xs.Nodup) (j : ℕ)
    (s : KoszulSlot xs.length j) : Set.range (koszulSlotTuple xs hxs j s)=
      (koszulSlotWedge xs j s : Set σ) := by
  ext x
  simp only [Set.mem_range,Finset.mem_coe]
  constructor
  · rintro ⟨i,rfl⟩
    rw [← koszulSlotList_toFinset]
    exact List.mem_toFinset.mpr (List.get_mem _ _)
  · intro hx
    rw [← koszulSlotList_toFinset,List.mem_toFinset] at hx
    obtain ⟨i,hi⟩ := List.mem_iff_get.mp hx
    refine ⟨Fin.cast (koszulSlotList_length xs j s) i,?_⟩
    change (koszulSlotList xs j s).get
      (Fin.cast (koszulSlotList_length xs j s).symm (Fin.cast (koszulSlotList_length xs j s) i))=x
    have he : Fin.cast (koszulSlotList_length xs j s).symm (Fin.cast (koszulSlotList_length xs j s) i)=i := Fin.ext rfl
    rw [he]
    exact hi

variable (k : Type) [Field k]
noncomputable def koszulSlotExterior (xs : List σ) (hxs : xs.Nodup) (j : ℕ)
    (s : KoszulSlot xs.length j) : ⋀[k]^j (σ → k) :=
  exteriorPower.ιMulti k j (fun i => Pi.single (koszulSlotTuple xs hxs j s i) 1)

noncomputable def koszulSlotExteriorDual (xs : List σ) (hxs : xs.Nodup) (j : ℕ)
    (s : KoszulSlot xs.length j) : Module.Dual k (⋀[k]^j (σ → k)) :=
  exteriorPower.pairingDual k (σ → k) j
    (exteriorPower.ιMulti k j (fun i => LinearMap.proj (koszulSlotTuple xs hxs j s i)))

theorem koszulSlotExteriorDual_diag (xs : List σ) (hxs : xs.Nodup) (j : ℕ)
    (s : KoszulSlot xs.length j) :
    koszulSlotExteriorDual k xs hxs j s (koszulSlotExterior k xs hxs j s)=1 := by
  unfold koszulSlotExteriorDual koszulSlotExterior
  rw [exteriorPower.pairingDual_ιMulti_ιMulti]
  have he : (Matrix.of (fun i l : Fin j =>
      (LinearMap.proj (koszulSlotTuple xs hxs j s l) : (σ → k) →ₗ[k] k)
        (Pi.single (koszulSlotTuple xs hxs j s i) 1)))=1 := by
    ext i l
    simp only [Matrix.of_apply,LinearMap.proj_apply,Pi.single_apply,Matrix.one_apply]
    congr 1
    exact propext ((koszulSlotTuple xs hxs j s).injective.eq_iff.trans eq_comm)
  rw [he,Matrix.det_one]

theorem koszulSlotExteriorDual_off (xs : List σ) (hxs : xs.Nodup) (j : ℕ)
    (s t : KoszulSlot xs.length j) (hst : s≠t) :
    koszulSlotExteriorDual k xs hxs j s (koszulSlotExterior k xs hxs j t)=0 := by
  have hnsub : ¬koszulSlotWedge xs j s⊆koszulSlotWedge xs j t := by
    intro hsub
    have he := Finset.eq_of_subset_of_card_le hsub (by
      rw [koszulSlotWedge_card xs hxs,koszulSlotWedge_card xs hxs])
    exact hst (koszulSlotWedge_injective xs hxs j he)
  obtain ⟨x,hxs',hxt⟩ := Finset.not_subset.mp hnsub
  obtain ⟨l,hl⟩ := (show x∈Set.range (koszulSlotTuple xs hxs j s) from
    (koszulSlotTuple_range xs hxs j s).symm ▸ hxs')
  unfold koszulSlotExteriorDual koszulSlotExterior
  rw [exteriorPower.pairingDual_ιMulti_ιMulti]
  apply Matrix.det_eq_zero_of_column_eq_zero l
  intro i
  simp only [Matrix.of_apply,LinearMap.proj_apply,Pi.single_apply]
  apply ite_eq_right
  intro hi
  apply hxt
  have hm : koszulSlotTuple xs hxs j t i∈koszulSlotWedge xs j t := by
    change koszulSlotTuple xs hxs j t i∈(koszulSlotWedge xs j t : Set σ)
    rw [← koszulSlotTuple_range xs hxs j t]
    exact ⟨i,rfl⟩
  rw [← hi,hl] at hm
  exact hm

theorem koszulSlotExterior_linearIndependent (xs : List σ) (hxs : xs.Nodup) (j : ℕ) :
    LinearIndependent k (koszulSlotExterior k xs hxs j) :=
  LinearIndependent.of_pairwise_dual_eq_zero_one _ (koszulSlotExteriorDual k xs hxs j)
    (fun s t h => koszulSlotExteriorDual_off k xs hxs j s t h)
    (fun s => koszulSlotExteriorDual_diag k xs hxs j s)

variable [Fintype σ]
noncomputable def koszulExteriorBasis (j : ℕ) :
    Module.Basis (KoszulSlot (variableList k σ).length j) k (⋀[k]^j (σ → k)) :=
  basisOfLinearIndependentOfCardEqFinrank' (koszulSlotExterior k (variableList k σ) (variableList_nodup k σ) j)
    (koszulSlotExterior_linearIndependent k _ (variableList_nodup k σ) j) (by
      rw [koszulSlot_card,variableList_length,exteriorPower.finrank_eq,Module.finrank_fintype_fun_eq_card])

theorem koszulExteriorBasis_apply (j : ℕ) (s : KoszulSlot (variableList k σ).length j) :
    koszulExteriorBasis (σ:=σ) k j s=koszulSlotExterior k (variableList k σ) (variableList_nodup k σ) j s := by
  unfold koszulExteriorBasis
  rw [coe_basisOfLinearIndependentOfCardEqFinrank']

noncomputable def koszulSlotWord {V : Type} [AddCommGroup V] [Module k V]
    (v : σ → V) (xs : List σ) (j : ℕ) (s : KoszulSlot xs.length j) : ExteriorAlgebra k V :=
  ((koszulSlotList xs j s).map (fun x => ExteriorAlgebra.ι k (v x))).prod

omit [Fintype σ] in
theorem koszulSlotExterior_coe (xs : List σ) (hxs : xs.Nodup) (j : ℕ)
    (s : KoszulSlot xs.length j) :
    (koszulSlotExterior k xs hxs j s : ExteriorAlgebra k (σ → k))=
      koszulSlotWord k (fun x : σ => Pi.single x 1) xs j s := by
  unfold koszulSlotExterior
  rw [exteriorPower.ιMulti_apply_coe,ExteriorAlgebra.ιMulti_apply]
  unfold koszulSlotWord
  congr 1
  apply List.ext_getElem
  · simp only [List.length_ofFn,List.length_map,koszulSlotList_length]
  · intro i hi hj
    simp only [List.getElem_ofFn,List.getElem_map,koszulSlotTuple,Function.Embedding.coeFn_mk,
      List.get_eq_getElem,Fin.val_cast]

variable {V : Type} [AddCommGroup V] [Module k V] (v : σ → V)

omit [Fintype σ] in
theorem koszulSlotWord_zero (xs : List σ) (s : KoszulSlot xs.length 0) :
    koszulSlotWord k v xs 0 s=1 := by
  have he : koszulSlotList xs 0 s=[] := List.eq_nil_of_length_eq_zero (koszulSlotList_length xs 0 s)
  simp only [koszulSlotWord,he,List.map_nil,List.prod_nil]

omit [Fintype σ] in
theorem koszulSlotWord_head (x : σ) (xs : List σ) (j : ℕ) (s : KoszulSlot xs.length j) :
    koszulSlotWord k v (x::xs) (j+1) (.inl s)=
      ExteriorAlgebra.ι k (v x)*koszulSlotWord k v xs j s := by
  simp only [koszulSlotWord,koszulSlotList,List.map_cons,List.prod_cons]

omit [Fintype σ] in
theorem koszulSlotWord_tail (x : σ) (xs : List σ) (j : ℕ) (s : KoszulSlot xs.length (j+1)) :
    koszulSlotWord k v (x::xs) (j+1) (.inr s)=koszulSlotWord k v xs (j+1) s := rfl

noncomputable def koszulArrowScalar (φ : Module.Dual k V) : Option (σ × Bool) → k
  | none => 0
  | some (x,false) => φ (v x)
  | some (x,true) => -φ (v x)

omit [Fintype σ] in
theorem koszulArrowScalar_flip (φ : Module.Dual k V) (a : Option (σ × Bool)) :
    koszulArrowScalar k v φ (a.map (fun b => (b.1,!b.2))) = -koszulArrowScalar k v φ a := by
  cases a with
  | none => simp only [Option.map_none,koszulArrowScalar,neg_zero]
  | some a => rcases a with ⟨x,b⟩; cases b <;> simp [koszulArrowScalar]

omit [Fintype σ] in
theorem koszulArrowScalar_ite (φ : Module.Dual k V) {α : Type} (s t : α) (x : σ) :
    koszulArrowScalar k v φ (if s=t then some (x,false) else none)=
      if s=t then φ (v x) else 0 := by
  by_cases h : s=t <;> simp only [h,ite_true,ite_false,koszulArrowScalar]

omit [Fintype σ] in
theorem koszulSlotWord_contraction (φ : Module.Dual k V) (xs : List σ) (j : ℕ)
    (s : KoszulSlot xs.length (j+1)) :
    CliffordAlgebra.contractLeft φ (koszulSlotWord k v xs (j+1) s)=
      ∑ t : KoszulSlot xs.length j,
        koszulArrowScalar k v φ (koszulSlotArrow xs j s t) • koszulSlotWord k v xs j t := by
  induction xs generalizing j with
  | nil => exact s.elim
  | cons x xs ih =>
    cases j with
    | zero => cases s with
      | inl s =>
        rw [koszulSlotWord_head,koszulSlotWord_zero,mul_one,CliffordAlgebra.contractLeft_ι]
        change algebraMap k (ExteriorAlgebra k V) (φ (v x))=
          ∑ t : KoszulSlot xs.length 0, koszulArrowScalar k v φ
            (if s=t then some (x,false) else none) • koszulSlotWord k v (x::xs) 0 t
        simp only [koszulArrowScalar_ite,ite_smul,zero_smul,
          Finset.sum_ite_eq,Finset.mem_univ,ite_true,koszulSlotWord_zero,Algebra.algebraMap_eq_smul_one]
      | inr s => exact ih 0 s
    | succ j => cases s with
      | inl s =>
        rw [koszulSlotWord_head,CliffordAlgebra.contractLeft_ι_mul,ih]
        change _=∑ t : KoszulSlot xs.length j ⊕ KoszulSlot xs.length (j+1), _
        rw [Fintype.sum_sum_type]
        simp only [koszulSlotArrow,koszulArrowScalar_flip,koszulSlotWord_head,koszulSlotWord_tail,
          koszulArrowScalar_ite,ite_smul,zero_smul,Finset.sum_ite_eq,Finset.mem_univ,ite_true,
          neg_smul,Finset.sum_neg_distrib]
        simp only [Finset.mul_sum,mul_smul_comm,sub_eq_add_neg,add_comm]
      | inr s =>
        change CliffordAlgebra.contractLeft φ (koszulSlotWord k v xs (j+2) s)=
          ∑ t : KoszulSlot xs.length j ⊕ KoszulSlot xs.length (j+1), _
        rw [Fintype.sum_sum_type]
        simp only [koszulSlotArrow,koszulArrowScalar,zero_smul,Finset.sum_const_zero,zero_add,koszulSlotWord_tail]
        exact ih (j+1) s
end NSP14.Homological
