module
public import NSP14.Width.TripleCorePoint
public import NSP14.Width.DenseHeight
public import NSP14.Endpoint.TwoMonomial
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open scoped Classical BigOperators
namespace NSP14.Endpoint.Data
variable (D : NSP14.Endpoint.Data)

def fiveHoleValues (flip : Bool) : Fin 3 → ℕ :=
  if flip then ![4,1,2] else ![1,3,4]

noncomputable def fiveHoleExponent (v : Fin 3 ≃ D.a) : Fin 5 → (D.a →₀ ℕ) :=
  ![Finsupp.single (v 0) 1+Finsupp.single (v 1) 1,
    Finsupp.single (v 0) 1+Finsupp.single (v 2) 1,
    Finsupp.single (v 1) 2,Finsupp.single (v 2) 2,Finsupp.single (v 0) 3]

/-- Four exact endpoint relations; these are verified in the original
integer core, not supplied as rank certificates. -/
def fiveHoleReduction (flip : Bool) : Fin 4 → ((ℕ×ℕ×ℕ)×(ℕ×ℕ)) :=
  if flip then ![((0,0,0),(1,1)),((0,1,0),(0,1)),((0,0,1),(1,0)),((1,0,0),(1,0))]
  else ![((0,0,1),(1,0)),((0,0,0),(1,1)),((1,0,0),(0,1)),((0,1,0),(0,1))]

theorem fiveHole_minimal_degree (hq : D.q=3) (hu : D.u=5) (p : D.CoreMinimalIndex) :
    D.coreDegree p.val ≤ 2 := by
  obtain ⟨w,hw⟩ := D.exists_coreWord p.val
  have hm : D.CoreMinimal (D.coreWord w) := by rw [hw]; exact p.property
  have hl := D.minimal_word_missing_bound w hm
  rw [hu,hq] at hl
  have hd := D.coreWord_degree w
  rw [hw] at hd
  omega

theorem fiveHole_quadratic_not_minimal (hu : D.u=5) (flip : Bool) (v : Fin 3 ≃ D.a)
    (hv : ∀ i,(v i).val=fiveHoleValues flip i) (i : Fin 4) :
    ¬D.CoreMinimal (D.internalPoint (D.fiveHoleExponent v i.castSucc)) := by
  let r := fiveHoleReduction flip i
  have hpos : 0<r.2.1+r.2.2 := by
    dsimp [r]
    cases flip <;> fin_cases i <;> norm_num [fiveHoleReduction]
  have hrel : D.internalPoint (D.fiveHoleExponent v i.castSucc)=
      D.triplePoint v r.1.1 r.1.2.1 r.1.2.2+D.coreEndpointPoint r.2 := by
    rw [D.triple_internalPoint v]
    apply Subtype.ext
    change (D.triplePoint v _ _ _).val=(D.triplePoint v _ _ _).val+(D.coreEndpointPoint _).val
    rw [D.triplePoint_coe,D.triplePoint_coe,D.coreEndpointPoint_coe,hu]
    simp_rw [hv]
    cases flip <;> fin_cases i <;>
      norm_num [r,fiveHoleReduction,fiveHoleExponent,fiveHoleValues,Finsupp.single_apply,v.injective.eq_iff]
  intro hm
  have he := D.minimal_endpoint_factor _ _ _ hm hrel
  have hz := congrArg (fun p : ℕ×ℕ => p.1+p.2) he
  change r.2.1+r.2.2=0 at hz
  omega

variable (k : Type) [Field k]
noncomputable def fiveHoleGenerator (v : Fin 3 ≃ D.a) (i : Fin 5) : D.InternalRing k :=
  MvPolynomial.monomial (D.fiveHoleExponent v i) 1

theorem fiveHole_generators_zero (hq : D.q=3) (hu : D.u=5) (flip : Bool)
    (v : Fin 3 ≃ D.a) (hv : ∀ i,(v i).val=fiveHoleValues flip i) (i : Fin 5) :
    D.internalToQCore k (D.fiveHoleGenerator k v i)=0 := by
  apply (D.QCore_internal_monomial_zero k _).mpr
  fin_cases i
  · exact D.fiveHole_quadratic_not_minimal hu flip v hv 0
  · exact D.fiveHole_quadratic_not_minimal hu flip v hv 1
  · exact D.fiveHole_quadratic_not_minimal hu flip v hv 2
  · exact D.fiveHole_quadratic_not_minimal hu flip v hv 3
  · intro hm
    have hd := D.fiveHole_minimal_degree hq hu ⟨_,hm⟩
    change D.coreDegree (D.internalPoint (D.fiveHoleExponent v 4)) ≤ 2 at hd
    rw [D.triple_internalPoint v,D.triplePoint_degree] at hd
    norm_num [fiveHoleExponent,Finsupp.single_apply,v.injective.eq_iff] at hd
end NSP14.Endpoint.Data
