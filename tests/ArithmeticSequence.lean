module
public import NSP14
@[expose] public section
open NSP14
namespace ArithmeticSequenceAcceptance
variable (D : ArithmeticSequence.Data)
theorem true_minimal_AP : D.source.embeddingDimension=D.v+1 := D.embeddingDimension
end ArithmeticSequenceAcceptance
