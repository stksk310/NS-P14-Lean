module
public import NSP14
@[expose] public section
namespace OrderedQuotientBasisAcceptance
open NSP14.Homological
variable {k I V : Type} [Field k] [LinearOrder I] [WellFoundedLT I]
  [AddCommGroup V] [Module k V]
variable (b : I → V) (hb : Submodule.span k (Set.range b)=⊤)
theorem actual_basis (i : OrderedStandards k b) : orderedStandardBasis k b hb i=b i.val :=
  orderedStandardBasis_apply k b hb i
end OrderedQuotientBasisAcceptance
