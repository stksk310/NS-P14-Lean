module
public import NSP14.Endpoint.CompetitorBounds
public import NSP14.Endpoint.Stopping
public import NSP14.Endpoint.Volume
@[expose] public section
open scoped BigOperators
namespace NSP14.Endpoint.Data
variable (D : NSP14.Endpoint.Data)
example : (∑ s : Fin D.u,D.competitorZ s)≤D.wordVolume-D.u := D.competitorZ_sum_bound
example (s : Fin D.u) : D.competitorZ s≤D.coreHeight-2 := D.competitorZ_height s
end NSP14.Endpoint.Data
