import Symmetry195
namespace SymmetryEdges195_5
open Symmetry195
set_option maxRecDepth 10000
set_option maxHeartbeats 0
theorem edges : ∀ v : Fin 32, ∀ k : Fin 8,
  Adj (partner (160+v.val))
    (partner (Nat.xor (160+v.val) (2^k.val))) ∧
  ¬ Adj (Nat.xor (160+v.val) (2^k.val)) (partner (160+v.val)) := by
  decide +kernel
#print axioms edges
end SymmetryEdges195_5
