module
public import NSP14.Endpoint.ArtinTransport
public import NSP14.Homological.ActionAppend
public import NSP14.Homological.RegularAugmentationBetti
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open scoped Classical
open CategoryTheory NSP14.Homological
namespace NSP14.Endpoint.Data
variable (D : NSP14.Endpoint.Data) (k : Type) [Field k]

noncomputable def internalVariableList : List D.a := variableList k D.a
noncomputable def fullVariableList : List D.Variables :=
  (D.internalVariableList k).map D.internalVariable++[D.vVariable,D.xVariable]

omit [Field k] in
theorem internalVariableList_length : (D.internalVariableList k).length=D.q := by
  simp only [internalVariableList,variableList_length,Fintype.card_coe,q]

omit [Field k] in
theorem fullVariableList_mem (b : D.Variables) : b∈D.fullVariableList k := by
  rcases (D.mem_offsets b.val).mp b.property with hb|hb|hb
  · apply List.mem_append_right
    have he : b=D.xVariable := Subtype.ext hb
    simp [he]
  · apply List.mem_append_right
    have he : b=D.vVariable := Subtype.ext hb
    simp [he]
  · apply List.mem_append_left
    exact List.mem_map.mpr ⟨⟨b.val,hb⟩,mem_variableList k D.a _,Subtype.ext rfl⟩

omit [Field k] in
theorem fullVariableList_nodup : (D.fullVariableList k).Nodup := by
  apply List.nodup_append.mpr
  refine ⟨(variableList_nodup k D.a).map D.internalVariable_injective,?_,?_⟩
  · have hne : D.vVariable≠D.xVariable := by
      intro h
      have hv := congrArg Subtype.val h
      change D.u=0 at hv
      have := D.u_pos
      omega
    simpa using hne
  · intro b hb c hc hbc
    subst c
    obtain ⟨a,_,rfl⟩ := List.mem_map.mp hb
    have hz : D.internalVariable a=D.vVariable ∨ D.internalVariable a=D.xVariable := by simpa using hc
    rcases hz with hz|hz
    · have h := congrArg Subtype.val hz
      have := D.a_lt a.val a.property
      change a.val=D.u at h
      omega
    · have h := congrArg Subtype.val hz
      have := D.a_pos a.val a.property
      change a.val=0 at h
      omega

theorem fullVariableList_actions : (D.fullVariableList k).map (fun b => D.fullToG k (MvPolynomial.X b))=
    (D.internalVariableList k).map (fun b => D.internalToG k (MvPolynomial.X b))++D.endpointElements k := by
  simp only [fullVariableList,List.map_append,List.map_map,List.map_cons,List.map_nil]
  congr 1
  · simp only [Function.comp_def,internalToG,AlgHom.comp_apply,internalToFull,MvPolynomial.rename_X]
  · simp only [endpointElements,endpointToG,AlgHom.comp_apply,endpointToFull,MvPolynomial.rename_X]
    rfl

noncomputable instance fullRegularFinite : Module.Finite (D.FullRing k)
    (polynomialRegularModule k D.Variables (D.source.TangentAlgebra k) (D.fullToG k)) := by
  apply regularPresentation_finite
  intro a
  obtain ⟨p,hp⟩ := D.source.fullPolynomialToG_surjective k a
  refine ⟨(D.fullPolynomialEquiv k).symm p,?_⟩
  change D.source.fullPolynomialToG k ((D.fullPolynomialEquiv k) ((D.fullPolynomialEquiv k).symm p))=a
  rw [AlgEquiv.apply_symm_apply,hp]
end NSP14.Endpoint.Data
