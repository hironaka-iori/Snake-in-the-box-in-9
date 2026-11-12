import Symmetry195
namespace SymmetryEdges195_0
open Symmetry195
set_option maxRecDepth 10000
set_option maxHeartbeats 0
theorem edges : ∀ v : Fin 32, ∀ k : Fin 8,
  Adj (partner (0+v.val))
    (partner (Nat.xor (0+v.val) (2^k.val))) ∧
  ¬ Adj (Nat.xor (0+v.val) (2^k.val)) (partner (0+v.val)) := by
  decide +kernel
#print axioms edges
end SymmetryEdges195_0
