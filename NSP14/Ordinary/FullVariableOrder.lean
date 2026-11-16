module
public import NSP14.Ordinary.FullVariableBetti
public import NSP14.Ordinary.NativeFullTransfer
public import NSP14.Homological.ActionAppend
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open NSP14.Homological
namespace NSP14.NumericalSemigroup.LinearCutData
variable {S : NumericalSemigroup} {k : Type} [Field k] (C : S.LinearCutData k)

noncomputable def extendedVariableOrder : List (Option (Fin (S.actualCutRank+C.complementRank))) :=
  (variableList k (Fin C.complementRank)).map (fun i => some (Fin.natAdd S.actualCutRank i)) ++
    none :: (variableList k (Fin S.actualCutRank)).map (fun i => some (Fin.castAdd C.complementRank i))

theorem extendedVariableOrder_all (a : Option (Fin (S.actualCutRank+C.complementRank))) : a∈C.extendedVariableOrder := by
  cases a with
  | none => exact List.mem_append_right _ List.mem_cons_self
  | some a =>
    by_cases ha : a.val<S.actualCutRank
    · apply List.mem_append_right
      apply List.mem_cons_of_mem
      exact List.mem_map.mpr ⟨⟨a.val,ha⟩,mem_variableList k _ _,congrArg some (Fin.ext rfl)⟩
    · apply List.mem_append_left
      have hf : a.val-S.actualCutRank<C.complementRank := by have := a.isLt;omega
      refine List.mem_map.mpr ⟨⟨a.val-S.actualCutRank,hf⟩,mem_variableList k _ _,?_⟩
      apply congrArg some
      apply Fin.ext
      change S.actualCutRank+(a.val-S.actualCutRank)=a.val
      omega

theorem extendedVariableOrder_nodup : C.extendedVariableOrder.Nodup := by
  have hc : Function.Injective (fun i : Fin C.complementRank => some (Fin.natAdd S.actualCutRank i)) := by
    intro a b h
    apply Fin.ext
    have hh := congrArg Fin.val (Option.some.inj h)
    change S.actualCutRank+a.val=S.actualCutRank+b.val at hh
    omega
  have hp : Function.Injective (fun i : Fin S.actualCutRank => some (Fin.castAdd C.complementRank i)) := by
    intro a b h
    have hh : Fin.castAdd C.complementRank a=Fin.castAdd C.complementRank b := Option.some.inj h
    have hv := congrArg (fun z : Fin (S.actualCutRank+C.complementRank) => z.val) hh
    exact Fin.ext hv
  apply List.nodup_append.mpr
  refine ⟨(variableList_nodup k _).map hc,List.nodup_cons.mpr ⟨?_,(variableList_nodup k _).map hp⟩,?_⟩
  · simp
  · intro a ha b hb hab
    subst b
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp ha
    rcases List.mem_cons.mp hb with h|h
    · cases h
    · obtain ⟨j,_,hj⟩ := List.mem_map.mp h
      have hh := congrArg Fin.val (Option.some.inj hj)
      change j.val=S.actualCutRank+i.val at hh
      have := j.isLt
      omega

theorem extendedFullToG_prefix (i : Fin S.actualCutRank) :
    C.extendedFullToG (MvPolynomial.X (some (Fin.castAdd C.complementRank i)))=C.nativeLambda i := by
  rw [C.extendedFullToG_some]
  change S.polynomialToG k (C.extendedPolynomialEquiv (MvPolynomial.X (Fin.castAdd C.complementRank i)))=_
  rw [C.extendedPolynomialEquiv_prefix]
  rfl

theorem extendedFullToG_complement (i : Fin C.complementRank) :
    C.extendedFullToG (MvPolynomial.X (some (Fin.natAdd S.actualCutRank i)))=
      C.complementPolynomialToG (MvPolynomial.X i) := by
  rw [C.extendedFullToG_some]
  change C.extendedPolynomialToG (MvPolynomial.X (Fin.natAdd S.actualCutRank i))=
    C.extendedPolynomialToG (MvPolynomial.rename (Fin.natAdd S.actualCutRank) (MvPolynomial.X i))
  rw [MvPolynomial.rename_X]

theorem extendedVariableOrder_action :
    C.extendedVariableOrder.map (fun a => C.extendedFullToG (MvPolynomial.X a))=
      (variableList k (Fin C.complementRank)).map (fun i => C.complementPolynomialToG (MvPolynomial.X i))++C.nativeCutVariables := by
  unfold extendedVariableOrder nativeCutVariables
  rw [List.map_append]
  apply congrArg₂ List.append
  · rw [List.map_map]
    apply List.map_congr_left
    intro i _
    exact C.extendedFullToG_complement i
  · rw [List.map_cons,C.extendedFullToG_none,List.map_map]
    congr 1
    apply List.map_congr_left
    intro i _
    exact C.extendedFullToG_prefix i
end NSP14.NumericalSemigroup.LinearCutData
