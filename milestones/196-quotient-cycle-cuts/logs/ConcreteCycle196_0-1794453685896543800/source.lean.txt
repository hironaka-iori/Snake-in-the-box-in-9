import CycleData196
namespace ConcreteCycle196_0
open LayerJoining CycleData196
set_option maxRecDepth 10000
set_option maxHeartbeats 0
theorem neighbours : ∀ i : Fin 36,
  cycle0 (prev i) ≠ cycle0 i ∧ cycle0 (next i) ≠ cycle0 i ∧
  cycle0 (prev i) ≠ cycle0 (next i) := by decide +kernel
theorem edges : ∀ i : Fin 36,
  Adj (cycle0 (prev i)) (cycle0 i) ∧ Adj (cycle0 (next i)) (cycle0 i) := by decide +kernel
theorem excluded {m : Nat} (p : InducedPath Nat Adj m) :
  ¬ (∀ i : Fin 36, ∃ j, p.vertex j=cycle0 i) :=
  CycleCut196.noContainedDegreeTwo p cycle0 prev next neighbours edges
#print axioms neighbours
#print axioms edges
#print axioms excluded
end ConcreteCycle196_0
