module
public import NSP14.ArithmeticSequence.ModelVariableOrder
public import NSP14.Homological.RegularModuleReduction
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory NSP14.Homological
open scoped Classical
namespace NSP14.ArithmeticSequence.Data
variable (D : NSP14.ArithmeticSequence.Data) (hv : 2 ≤ D.v)

noncomputable def modelOptionFinEquiv : Option (Fin (D.v-1)) ≃ Fin D.v where
  toFun
    | none => ⟨D.v-1,by omega⟩
    | some i => ⟨i.val,by have := i.isLt;omega⟩
  invFun i := if h : i.val=D.v-1 then none else some ⟨i.val,by have := i.isLt;omega⟩
  left_inv a := by
    cases a with
    | none => simp
    | some i =>
      dsimp only
      rw [dite_eq_right (by have := i.isLt;omega)]
  right_inv i := by
    dsimp only
    split_ifs with h
    · exact Fin.ext h.symm
    · rfl

variable (k : Type) [Field k]
noncomputable def modelFullOrder : List (Fin D.v) :=
  (fullOptionOrder k (Fin (D.v-1))).map (D.modelOptionFinEquiv hv)

omit [Field k] in
theorem modelFullOrder_all (i : Fin D.v) : i∈D.modelFullOrder hv k := by
  obtain ⟨a,rfl⟩ := (D.modelOptionFinEquiv hv).surjective i
  exact List.mem_map.mpr ⟨a,fullOptionOrder_all k (Fin (D.v-1)) a,rfl⟩

omit [Field k] in
theorem modelFullOrder_nodup : (D.modelFullOrder hv k).Nodup :=
  (fullOptionOrder_nodup k (Fin (D.v-1))).map (D.modelOptionFinEquiv hv).injective

theorem modelFullOrder_action :
    (D.modelFullOrder hv k).map (fun j => D.modelFullPolynomial hv k (MvPolynomial.X j))=
      (D.ordinaryModel hv).source.xElement k::
        (variableList k (Fin (D.v-1))).map (fun j => D.modelWindowPolynomial hv k (MvPolynomial.X j)) := by
  unfold modelFullOrder fullOptionOrder
  rw [List.map_map,List.map_cons]
  apply congrArg₂ List.cons
  · change D.modelFullPolynomial hv k (MvPolynomial.X ⟨D.v-1,by omega⟩)=_
    rw [D.modelFullPolynomial_X,Nat.sub_add_cancel (show 1 ≤ D.v by omega),← D.modelMultiplicityMonomial hv k]
  · rw [List.map_map]
    apply List.map_congr_left
    intro j _
    change D.modelFullPolynomial hv k (MvPolynomial.X ⟨j.val,by have := j.isLt;omega⟩)=_
    rw [D.modelFullPolynomial_X,modelWindowPolynomial,MvPolynomial.aeval_X]

noncomputable abbrev modelFullRestricted (N : ModuleCat ((D.ordinaryModel hv).source.TangentAlgebra k)) :
    ModuleCat (VariableRing k (Fin D.v)) :=
  (ModuleCat.restrictScalars (D.modelFullPolynomial hv k).toRingHom).obj N

/-- Ordinary full-variable Tor of an actual native module is computed
with the explicit order x followed by all remaining actual variables. -/
noncomputable def modelFullNativeHomologyIso
    (N : ModuleCat ((D.ordinaryModel hv).source.TangentAlgebra k)) (i : ℕ) :
    (actionCoefficientComplex k ((D.ordinaryModel hv).source.TangentAlgebra k)
      (((D.ordinaryModel hv).source.xElement k)::
        (variableList k (Fin (D.v-1))).map (fun j => D.modelWindowPolynomial hv k (MvPolynomial.X j))) N).homology i ≅
      koszulHomologyK k (Fin D.v) (D.modelFullRestricted hv k N) i := by
  have e := actionFullPolynomialHomologyIso ((D.ordinaryModel hv).source.TangentAlgebra k) N k
    (Fin D.v) (D.modelFullPolynomial hv k) (D.modelFullOrder hv k)
    (D.modelFullOrder_all hv k) (D.modelFullOrder_nodup hv k) i
  rw [D.modelFullOrder_action hv k] at e
  exact e
end NSP14.ArithmeticSequence.Data
