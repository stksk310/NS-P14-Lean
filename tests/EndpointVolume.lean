module
public import NSP14.Endpoint.Volume
public import NSP14.Endpoint.MinimalGenerators
@[expose] public section
namespace NSP14.Endpoint.Data
variable (D : NSP14.Endpoint.Data)
theorem EndpointVolume_acceptance_001 : (∑ r : Fin D.u,(D.minimalPoints r).card)≤1+∑ r : Fin D.u,D.shortestDegree r := D.minimalCount_volume
end NSP14.Endpoint.Data
