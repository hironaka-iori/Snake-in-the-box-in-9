import CycleData196
namespace ConcreteCycle196_1
open LayerJoining CycleData196
set_option maxRecDepth 10000
set_option maxHeartbeats 0
theorem neighbours : ∀ i : Fin 36,
  cycle1 (prev i) ≠ cycle1 i ∧ cycle1 (next i) ≠ cycle1 i ∧
  cycle1 (prev i) ≠ cycle1 (next i) := by decide +kernel
theorem edges : ∀ i : Fin 36,
  Adj (cycle1 (prev i)) (cycle1 i) ∧ Adj (cycle1 (next i)) (cycle1 i) := by decide +kernel
theorem excluded {m : Nat} (p : InducedPath Nat Adj m) :
  ¬ (∀ i : Fin 36, ∃ j, p.vertex j=cycle1 i) :=
  CycleCut196.noContainedDegreeTwo p cycle1 prev next neighbours edges
#print axioms neighbours
#print axioms edges
#print axioms excluded
end ConcreteCycle196_1
