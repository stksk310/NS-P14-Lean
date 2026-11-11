module
public import NSP14.Endpoint.Socle
@[expose] public section
namespace NSP14.Endpoint.Data
variable (D : NSP14.Endpoint.Data) (k : Type) [Field k]
example : D.actualR k=Module.finrank k (D.actualSocle k) := D.actualR_socle_dimension k
end NSP14.Endpoint.Data
