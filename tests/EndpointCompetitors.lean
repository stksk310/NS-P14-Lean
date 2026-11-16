module
public import NSP14
@[expose] public section
open NSP14
namespace EndpointCompetitorsAcceptance
variable (D : Endpoint.Data)

theorem all_longer_representations (p : D.corePoints) :
    D.coreDegree p<D.source.order (D.coreValue p).val ↔
      ∃ j : ℕ,1≤j ∧ ∃ q : D.corePoints,
        D.coreDegree q=D.coreDegree p+j*D.d ∧ D.coreOffset p=D.coreOffset q+j*D.m :=
  D.core_dead_iff_competitor p
end EndpointCompetitorsAcceptance
