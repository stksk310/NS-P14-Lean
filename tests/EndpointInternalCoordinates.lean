module
public import NSP14.Endpoint.InternalCoordinates
@[expose] public section
namespace NSP14.Endpoint.Data
theorem EndpointInternalCoordinates_acceptance_001 (D : Data) (b : D.a) (p : D.corePoints) (r s : Fin D.u) (L K c : ℕ)
    (hp : D.coreCoordinates p=(r,L,K)) (hc : r.val+b.val=s.val+D.u*c) :
    D.coreCoordinates (p+D.coreGeneratorPoint (D.internalVariable b))=
      (s,L+1+D.epsilon r-c-D.epsilon s,K+c) := D.internal_coordinate_step b p r s L K c hp hc
end NSP14.Endpoint.Data
