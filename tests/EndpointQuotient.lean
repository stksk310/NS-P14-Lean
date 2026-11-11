module
public import NSP14.Endpoint.Quotient
public import NSP14.Endpoint.FiberModule
public import NSP14.Endpoint.KernelIdeals
@[expose] public section
open scoped DirectSum
namespace NSP14.Endpoint.Data
variable (D : NSP14.Endpoint.Data) (k : Type) [Field k]
example (f : ⨁ r : Fin D.u,D.coreFiberIdeal k r) :
    D.coreToG k (D.coreFiberLinearAssembly k f)=0 ↔
      ∀ r,(f r).val∈D.actualKernelIdeal k r := D.assembled_kernel_iff k f
end NSP14.Endpoint.Data
