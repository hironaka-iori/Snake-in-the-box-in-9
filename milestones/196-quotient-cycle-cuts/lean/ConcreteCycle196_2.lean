import CycleData196
namespace ConcreteCycle196_2
open LayerJoining CycleData196
set_option maxRecDepth 10000
set_option maxHeartbeats 0
theorem neighbours : ∀ i : Fin 36,
  cycle2 (prev i) ≠ cycle2 i ∧ cycle2 (next i) ≠ cycle2 i ∧
  cycle2 (prev i) ≠ cycle2 (next i) := by decide +kernel
theorem edges : ∀ i : Fin 36,
  Adj (cycle2 (prev i)) (cycle2 i) ∧ Adj (cycle2 (next i)) (cycle2 i) := by decide +kernel
theorem excluded {m : Nat} (p : InducedPath Nat Adj m) :
  ¬ (∀ i : Fin 36, ∃ j, p.vertex j=cycle2 i) :=
  CycleCut196.noContainedDegreeTwo p cycle2 prev next neighbours edges
#print axioms neighbours
#print axioms edges
#print axioms excluded
end ConcreteCycle196_2
