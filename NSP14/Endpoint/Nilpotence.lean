module
public import NSP14.Endpoint.FiberModule
@[expose] public section
set_option backward.isDefEq.respectTransparency false
namespace NSP14.Endpoint.Data
variable (D : NSP14.Endpoint.Data)

theorem coreEndpointPoint_degree (c : ℕ×ℕ) : D.coreDegree (D.coreEndpointPoint c)=c.1+c.2 :=
  congrArg Prod.fst (D.coreEndpointPoint_coe c)

theorem coreEndpointPoint_offset (c : ℕ×ℕ) : D.coreOffset (D.coreEndpointPoint c)=D.u*c.2 :=
  congrArg Prod.snd (D.coreEndpointPoint_coe c)

theorem endpoint_v_power_dead :
    D.coreDegree (D.coreEndpointPoint (0,D.m))<
      D.source.order (D.coreValue (D.coreEndpointPoint (0,D.m))).val := by
  apply (D.core_dead_iff_competitor (D.coreEndpointPoint (0,D.m))).mpr
  refine ⟨D.u,D.u_pos,D.coreEndpointPoint (D.m+D.u*D.d,0),?_,?_⟩
  · rw [D.coreEndpointPoint_degree,D.coreEndpointPoint_degree]
    simp
  · rw [D.coreEndpointPoint_offset,D.coreEndpointPoint_offset]
    simp

variable (k : Type) [Field k]

theorem coreMonomial_pow (p : D.corePoints) (n : ℕ) :
    D.coreMonomial k p^n=D.coreMonomial k (n • p) := by
  simp only [coreMonomial,AddMonoidAlgebra.single_pow,one_pow]

/-- v^m is zero in the same actual tangent cone: its numerical exponent
has the genuinely longer x-only representation of length m+d*u. -/
theorem endpoint_v_nilpotent : D.endpointToG k (MvPolynomial.X (1 : Fin 2))^D.m=0 := by
  have h := AlgHom.congr_fun (D.coreToG_endpointToCore k) (MvPolynomial.X (1 : Fin 2))
  change D.coreToG k (D.endpointToCore k (MvPolynomial.X (1 : Fin 2)))=
    D.endpointToG k (MvPolynomial.X (1 : Fin 2)) at h
  rw [← h,← map_pow,D.endpointToCore_X,D.coreMonomial_pow]
  have hv : D.endpointVariable (1 : Fin 2)=D.vVariable := by simp [endpointVariable]
  rw [hv]
  have hp : D.m • D.coreGeneratorPoint D.vVariable=D.coreEndpointPoint (0,D.m) := by
    simp only [coreEndpointPoint,zero_nsmul,zero_add]
  rw [hp]
  exact (D.coreToG_monomial_zero_iff k _).mpr D.endpoint_v_power_dead
end NSP14.Endpoint.Data
