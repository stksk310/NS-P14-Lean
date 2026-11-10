module
public import NSP14
@[expose] public section
namespace ArithmeticSequenceOrderAcceptance
open NSP14.ArithmeticSequence
variable (D : Data)
theorem canonical_order (n i : ℕ) (hi : i < D.m) (hni : i ≤ D.v*n) :
    D.source.order (n*D.m+i*D.d)=n := D.canonical_order n i hi hni

theorem x_stable {x : ℕ} (hx : x ∈ D.source) :
    D.source.order (x+D.m)=D.source.order x+1 := D.order_add_m hx
end ArithmeticSequenceOrderAcceptance
