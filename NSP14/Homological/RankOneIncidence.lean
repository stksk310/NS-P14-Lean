module
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
@[expose] public section
open scoped BigOperators Classical
namespace NSP14.Homological
variable (k : Type*) [Field k] (I J V U : Type*) [Fintype I] [Fintype J]
  [AddCommGroup V] [Module k V] [AddCommGroup U] [Module k U]
  (active : I → J → Prop)
  (ell : I → J → V →ₗ[k] k) (u : I → J → U)

noncomputable def rankOneIncidence : (I → V) →ₗ[k] (J → U) where
  toFun c j := ∑ i : {i // active i j}, ell i.val j (c i.val) • u i.val j
  map_add' c d := by ext j;simp only [Pi.add_apply,map_add,add_smul,Finset.sum_add_distrib]
  map_smul' r c := by
    ext j
    simp only [Pi.smul_apply,map_smul,smul_eq_mul,mul_smul,Finset.smul_sum,RingHom.id_apply]

omit [Fintype J] in
/-- A rank-one incidence map is injective if the active image vectors at
one row are independent and the active functionals at one column separate
points. This is ordinary linear algebra on actual finite sums. -/
theorem rankOneIncidence_injective
    (hrow : ∀ j,LinearIndependent k (fun i : {i // active i j} => u i.val j))
    (hcol : ∀ i (c : V),(∀ j,active i j → ell i j c=0) → c=0) :
    Function.Injective (rankOneIncidence k I J V U active ell u) := by
  apply LinearMap.ker_eq_bot.mp
  apply (Submodule.eq_bot_iff _).mpr
  intro c hc
  have hz (j : J) : ∑ i : {i // active i j},ell i.val j (c i.val) • u i.val j=0 :=
    congrFun hc j
  have hzero (i : I) (j : J) (hij : active i j) : ell i j (c i)=0 :=
    (Fintype.linearIndependent_iff.mp (hrow j)) _ (hz j) ⟨i,hij⟩
  funext i
  exact hcol i (c i) (hzero i)

omit [Fintype J] in
theorem sum_active (j : J) (f : I → U) :
    (∑ i : {i // active i j},f i.val)=∑ i,if active i j then f i else 0 := by
  rw [← Finset.sum_filter]
  exact (Finset.sum_subtype _ (by simp) f).symm

omit [Fintype J] in
theorem rankOneIncidence_apply (c : I → V) (j : J) :
    rankOneIncidence k I J V U active ell u c j=
      ∑ i,if active i j then ell i j (c i) • u i j else 0 :=
  sum_active I J U active j (fun i => ell i j (c i) • u i j)

omit [Fintype J] in
theorem rankOneIncidence_single (i : I) (v : V) (j : J) :
    rankOneIncidence k I J V U active ell u (Pi.single i v) j=
      if active i j then ell i j v • u i j else 0 := by
  rw [rankOneIncidence_apply]
  rw [Fintype.sum_eq_single i]
  · simp only [Pi.single_eq_same]
  · intro z hz
    simp [Pi.single_eq_of_ne hz]

theorem linearForm_apply_pi_sum (phi : (J → U) →ₗ[k] k) (c : J → U) :
    phi c=∑ j,phi (Pi.single j (c j)) := by
  have h : (∑ j,Pi.single j (c j))=c := by ext j;simpa only [Finset.sum_apply] using Fintype.sum_pi_single j c
  calc
    phi c=phi (∑ j,Pi.single j (c j)) := congrArg phi h.symm
    _=∑ j,phi (Pi.single j (c j)) := map_sum phi _ _

theorem rankOneIncidence_surjective
    (hcol : ∀ i,LinearIndependent k (fun j : {j // active i j} => ell i j.val))
    (hrow : ∀ j (f : U →ₗ[k] k),(∀ i,active i j → f (u i j)=0) → f=0) :
    Function.Surjective (rankOneIncidence k I J V U active ell u) := by
  apply LinearMap.dualMap_injective_iff.mp
  apply LinearMap.ker_eq_bot.mp
  apply (Submodule.eq_bot_iff _).mpr
  intro phi hphi
  let form (j : J) : U →ₗ[k] k := phi.comp (LinearMap.single k (fun _ : J => U) j)
  have hz (i : I) : ∑ j : {j // active i j},form j.val (u i j.val) • ell i j.val=0 := by
    apply LinearMap.ext
    intro v
    have he := LinearMap.congr_fun hphi (Pi.single i v)
    change phi (rankOneIncidence k I J V U active ell u (Pi.single i v))=0 at he
    rw [linearForm_apply_pi_sum] at he
    simp only [rankOneIncidence_single] at he
    simp only [LinearMap.sum_apply,LinearMap.smul_apply,smul_eq_mul,LinearMap.zero_apply]
    change (∑ j : {j // active i j},form j.val (u i j.val)*ell i j.val v)=0
    rw [sum_active J I k (fun j i => active i j) i (fun j => form j (u i j)*ell i j v)]
    convert he using 1
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : active i j
    · simp only [hj,ite_true]
      change form j (u i j)*ell i j v=phi (Pi.single j (ell i j v • u i j))
      rw [Pi.single_smul,map_smul]
      exact mul_comm _ _
    · simp [hj]
  have hzero (i : I) (j : J) (hij : active i j) : form j (u i j)=0 :=
    (Fintype.linearIndependent_iff.mp (hcol i)) _ (hz i) ⟨j,hij⟩
  have hf (j : J) : form j=0 := hrow j (form j) (fun i hi => hzero i j hi)
  apply LinearMap.ext
  intro c
  rw [linearForm_apply_pi_sum]
  apply Finset.sum_eq_zero
  intro j _
  exact LinearMap.congr_fun (hf j) (c j)
end NSP14.Homological
