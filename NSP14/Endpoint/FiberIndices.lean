module
public import NSP14.Endpoint.IdealCoordinates
@[expose] public section
namespace NSP14.Endpoint

/-- The two endpoint exponent coordinates, additively and without a
choice of a different polynomial action. -/
noncomputable def exponentPairEquiv : (ℕ×ℕ) ≃+ (Fin 2 →₀ ℕ) where
  toFun c := Finsupp.single 0 c.1+Finsupp.single 1 c.2
  invFun b := (b 0,b 1)
  left_inv c := by
    apply Prod.ext <;> simp
  right_inv b := by
    ext i
    have hi : i=0 ∨ i=1 := by
      by_cases h : i.val=0
      · exact Or.inl (Fin.ext h)
      · exact Or.inr (Fin.ext (by have := i.isLt;omega))
    rcases hi with rfl|rfl <;> simp
  map_add' c d := by
    change Finsupp.single 0 (c.1+d.1)+Finsupp.single 1 (c.2+d.2)=_
    simp only [Finsupp.single_add]
    abel
end NSP14.Endpoint
namespace NSP14.Endpoint.Data
variable (D : NSP14.Endpoint.Data)
def FiberPoint (r : Fin D.u) := {c : ℕ×ℕ // c∈D.coreFiber r}

noncomputable def fiberExponentEquiv (r : Fin D.u) :
    {b : Fin 2 →₀ ℕ // (b 0,b 1)∈D.coreFiber r} ≃ D.FiberPoint r where
  toFun b := ⟨(b.val 0,b.val 1),b.property⟩
  invFun c := ⟨NSP14.Endpoint.exponentPairEquiv c.val,by
    change (NSP14.Endpoint.exponentPairEquiv.symm (NSP14.Endpoint.exponentPairEquiv c.val))∈D.coreFiber r
    rw [AddEquiv.symm_apply_apply]
    exact c.property⟩
  left_inv b := Subtype.ext (NSP14.Endpoint.exponentPairEquiv.apply_symm_apply b.val)
  right_inv c := Subtype.ext (NSP14.Endpoint.exponentPairEquiv.symm_apply_apply c.val)

def coordinateFiberEquiv : D.CoordinatePoint ≃ (Σ r : Fin D.u,D.FiberPoint r) where
  toFun c := ⟨c.val.1,⟨c.val.2,c.property⟩⟩
  invFun c := ⟨(c.1,c.2.val),c.2.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

variable (k : Type) [Field k]
noncomputable def coreFiberPairCoefficients (r : Fin D.u) :
    (D.coreFiberIdeal k r) ≃ₗ[k] (D.FiberPoint r →₀ k) :=
  (D.coreFiberCoefficients k r).trans (Finsupp.domLCongr (R:=k) (M:=k) (D.fiberExponentEquiv r))
end NSP14.Endpoint.Data
