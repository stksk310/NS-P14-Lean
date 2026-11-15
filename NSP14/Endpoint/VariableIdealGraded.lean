module
public import NSP14.Endpoint.ArtinGradedZero
public import NSP14.Endpoint.GradedIdealAdjoining
public import NSP14.Homological.VariableIdealBetti
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open scoped Classical
open CategoryTheory NSP14.Homological
attribute [local instance] MvPolynomial.gradedAlgebra
namespace NSP14.Endpoint
variable (k σ : Type) [Field k] [Fintype σ] [LinearOrder σ]

omit [Fintype σ] [LinearOrder σ] in
theorem variablesIdeal_homogeneous (xs : List σ) :
    (variablesIdeal k σ xs).IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k) := by
  unfold variablesIdeal
  apply Ideal.homogeneous_span
  rintro _ ⟨x,_,rfl⟩
  exact ⟨1,MvPolynomial.isHomogeneous_X (R:=k) x⟩

omit [Fintype σ] [LinearOrder σ] in
theorem variablesIdeal_colon (xs : List σ) (x : σ) (hx : x ∉ xs) :
    (variablesIdeal k σ xs).colon {MvPolynomial.X x}=variablesIdeal k σ xs := by
  have hp : (variablesIdeal k σ xs).IsPrime := MvPolynomial.span_X_image_isPrime _
  ext a
  constructor
  · intro ha
    have hm : a*MvPolynomial.X x ∈ variablesIdeal k σ xs := Submodule.mem_colon_singleton.mp ha
    exact (hp.mem_or_mem hm).resolve_right (variable_not_mem_variablesIdeal k σ xs x hx)
  · intro ha
    apply Submodule.mem_colon_singleton.mpr
    exact (variablesIdeal k σ xs).mul_mem_right (MvPolynomial.X x) ha

noncomputable def coordinateGradedBetti (xs : List σ) (i : ℕ) (t : ℤ) : ℕ :=
  gradedBetti k σ (artinModule k σ (variablesIdeal k σ xs))
    (artinGrading k σ (variablesIdeal k σ xs) (variablesIdeal_homogeneous k σ xs)) i t

theorem coordinateGradedBetti_zero (xs : List σ) (t : ℤ) :
    coordinateGradedBetti k σ xs 0 t=if (0:ℤ)=t then 1 else 0 := by
  have hp : (variablesIdeal k σ xs).IsPrime := MvPolynomial.span_X_image_isPrime _
  exact artin_gradedBetti_zero k σ (variablesIdeal k σ xs) hp.ne_top (variablesIdeal_homogeneous k σ xs) t

/-- Each coordinate variable is added through its actual homogeneous
colon sequence. The same previous quotient supplies the shifted term. -/
theorem coordinateGradedBetti_cons (xs : List σ) (x : σ) (hx : x ∉ xs) (i : ℕ) (t : ℤ) :
    coordinateGradedBetti k σ (x::xs) (i+1) t=
      coordinateGradedBetti k σ xs (i+1) t+coordinateGradedBetti k σ xs i (t-1) := by
  let J := variablesIdeal k σ xs
  let g : MvPolynomial σ k := MvPolynomial.X x
  have hJ := variablesIdeal_homogeneous k σ xs
  have hK : (J ⊔ Ideal.span {g}).IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k) :=
    hJ.sup (by
      apply Ideal.homogeneous_span
      rintro _ rfl
      exact ⟨1,MvPolynomial.isHomogeneous_X (R:=k) x⟩)
  have hcol : J.colon {g}=J := variablesIdeal_colon k σ xs x hx
  have hC : (J.colon {g}).IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k) := by
    rw [hcol]
    exact hJ
  have hc : J.colon {g} ≤ J.colon {(1:MvPolynomial σ k)} := by
    intro a ha
    apply Submodule.mem_colon_singleton.mpr
    change a*1 ∈ J
    rw [mul_one]
    exact hcol ▸ ha
  have hh := artin_adjoin_gradedBetti k σ J g 1 x hJ hK hC 1
    (MvPolynomial.isHomogeneous_X (R:=k) x) (by exact (mul_one g).symm) hc i t
  have he : J ⊔ Ideal.span {g}=variablesIdeal k σ (x::xs) := by
    rw [variablesIdeal_cons,sup_comm]
  have hnew := artinGradedBetti_congr k σ (J ⊔ Ideal.span {g}) (variablesIdeal k σ (x::xs))
    hK (variablesIdeal_homogeneous k σ (x::xs)) he (i+1) t
  have hold := artinGradedBetti_congr k σ (J.colon {g}) J hC hJ hcol i (t-(1:ℤ))
  simp only [Nat.cast_one] at hh
  rw [hnew,hold] at hh
  exact hh

theorem coordinateGradedBetti_formula (xs : List σ) : xs.Nodup → ∀ (i : ℕ) (t : ℤ),
    coordinateGradedBetti k σ xs i t=if (i:ℤ)=t then xs.length.choose i else 0 := by
  induction xs with
  | nil =>
    intro _ i t
    cases i with
    | zero => simpa only [Nat.cast_zero,Nat.choose_zero_right] using coordinateGradedBetti_zero k σ [] t
    | succ i =>
      have hl := gradedBetti_le_total k σ (artinModule k σ (variablesIdeal k σ []))
        (artinGrading k σ (variablesIdeal k σ []) (variablesIdeal_homogeneous k σ [])) (i+1) t
      have ht := variable_ideal_betti k σ [] (by simp) (i+1)
      rw [ht] at hl
      have hi : 0 < i+1 := by omega
      simp only [List.length_nil,Nat.choose_eq_zero_of_lt hi] at hl
      have hz : coordinateGradedBetti k σ [] (i+1) t=0 := Nat.eq_zero_of_le_zero hl
      change coordinateGradedBetti k σ [] (i+1) t=if ((i+1:ℕ):ℤ)=t then [].length.choose (i+1) else 0
      rw [hz]
      simp only [List.length_nil,Nat.choose_eq_zero_of_lt hi,ite_self]
  | cons x xs ih =>
    intro hn i t
    cases i with
    | zero => simpa only [Nat.cast_zero,Nat.choose_zero_right] using coordinateGradedBetti_zero k σ (x::xs) t
    | succ i =>
      rw [coordinateGradedBetti_cons k σ xs x (List.nodup_cons.mp hn).1 i t,
        ih (List.nodup_cons.mp hn).2 (i+1) t,ih (List.nodup_cons.mp hn).2 i (t-1)]
      by_cases h : (i:ℤ)+1=t
      · have h' : (i:ℤ)=t-1 := by omega
        simp only [Nat.cast_add,Nat.cast_one,h',sub_add_cancel,ite_true,List.length_cons]
        rw [Nat.choose_succ_succ]
        simp only [Nat.succ_eq_add_one]
        omega
      · have h' : (i:ℤ) ≠ t-1 := by omega
        simp only [Nat.cast_add,Nat.cast_one,h,h',ite_false,zero_add]

/-- Actual graded Betti formula for every coordinate quotient, with
the given actual homogeneous-ideal witness and no Artinian assumption. -/
theorem variable_ideal_gradedBetti (xs : List σ) (hx : xs.Nodup)
    (hI : (variablesIdeal k σ xs).IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k))
    (i : ℕ) (t : ℤ) :
    gradedBetti k σ (artinModule k σ (variablesIdeal k σ xs))
      (artinGrading k σ (variablesIdeal k σ xs) hI) i t=
      if (i:ℤ)=t then xs.length.choose i else 0 :=
  coordinateGradedBetti_formula k σ xs hx i t

end NSP14.Endpoint
