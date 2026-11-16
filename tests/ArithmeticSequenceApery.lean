module
public import NSP14
@[expose] public section
namespace ArithmeticSequenceAperyAcceptance
open NSP14.ArithmeticSequence
variable (D : Data)
theorem actual_apery (i : ℕ) (hi : i < D.m) :
    D.aperyValue i ∈ D.source.aperySet := D.aperyValue_mem hi
end ArithmeticSequenceAperyAcceptance
