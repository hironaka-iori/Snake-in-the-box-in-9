import BalancedGraphData

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Shared89
open Snake9.Boxes88 Snake9.Certificate88 Snake9.Balanced89

theorem graphTable_valid : check graphTable = true := by decide +kernel

theorem graphTable_flat : flatten graphTable = retainedDiagram.toList := by decide +kernel

def advanceBalanced (node symbol : Nat) : Nat :=
  if node < 2 then node else (lookup graphTable (node-2) #[]).getD symbol 0

theorem advanceBalanced_eq (node symbol : Nat) :
    advanceBalanced node symbol = nextNode retainedDiagram node symbol := by
  simp only [advanceBalanced, nextNode,
    lookup_eq_list graphTable retainedDiagram.toList graphTable_valid graphTable_flat]
  simp only [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD, Array.getElem?_toList]

#print axioms graphTable_valid
#print axioms graphTable_flat
#print axioms advanceBalanced_eq

end Snake9.Shared89
