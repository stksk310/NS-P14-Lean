module
public import NSP14.Endpoint.CoreArtinBasis
public import NSP14.Endpoint.CoreArtinIdeal
public import NSP14.Endpoint.Volume
@[expose] public section
namespace NSP14.Endpoint.Data
variable (D : NSP14.Endpoint.Data) (k : Type) [Field k]
example : D.coreP k≤D.wordVolume := D.coreP_le_wordVolume k
example : D.coreP k=∑ r : Fin D.u,(D.minimalPoints r).card := D.coreP_minimalCount k
end NSP14.Endpoint.Data
