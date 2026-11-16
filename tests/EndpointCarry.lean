module
public import NSP14
@[expose] public section
open NSP14
namespace EndpointCarryAcceptance
variable (D : Endpoint.Data)

theorem carry_reconstruction (r : Fin D.u) (j : ℕ) :
    r.val+j*D.m=(D.shiftedResidue r j).val+D.u*D.carry r j := D.carry_eq r j

theorem decay (r : Fin D.u) (j L K H : ℕ) (hL : L≤H) :
    (D.forbiddenStart r j (L,K)).1≤H-2*j := D.forbiddenStart_height r j L K H hL
end EndpointCarryAcceptance
