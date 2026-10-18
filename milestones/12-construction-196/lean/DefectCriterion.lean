import Snake9
import Mathlib.Tactic

namespace Snake9.DefectConstruction
open scoped BigOperators

/-- Duplicate vertices have weight four; nonconsecutive adjacent pairs have weight one. -/
def pairDefect {m : Nat} (f : Fin (m+1) → Vertex) (i j : Fin (m+1)) : Nat :=
  if i.val < j.val then
    if f i = f j then 4 else if i.val+1 ≠ j.val ∧ Adj (f i) (f j) then 1 else 0
  else 0

def energy {m : Nat} (f : Fin (m+1) → Vertex) : Nat :=
  ∑ i, ∑ j, pairDefect f i j

/-- A zero-energy adjacent walk is a snake under the project's original definition. -/
def snakeOfZeroEnergy {m : Nat} (f : Fin (m+1) → Vertex)
    (walk : ∀ i j, i.val+1 = j.val → Adj (f i) (f j))
    (zero : energy f = 0) : Snake m := by
  have hz : ∀ i j, pairDefect f i j = 0 := by
    simpa only [energy, Finset.sum_eq_zero_iff, Finset.mem_univ, true_implies] using zero
  have distinct : ∀ i j, f i = f j → i = j := by
    intro i j he
    apply Fin.ext
    by_contra hn
    rcases Nat.lt_or_gt_of_ne hn with hi | hi
    · have h := hz i j
      simp [pairDefect,hi,he] at h
    · have h := hz j i
      simp [pairDefect,hi,he] at h
  refine ⟨f,distinct,?_⟩
  intro i j hij
  constructor
  · intro ha
    by_contra hstep
    have hn : f i ≠ f j := by
      intro he
      have := congrArg Fin.val (distinct i j he)
      omega
    have h := hz i j
    simp [pairDefect,hij,hn,hstep,ha] at h
  · exact walk i j

theorem snake_energy_zero {m : Nat} (p : Snake m) : energy p.vertex = 0 := by
  apply Finset.sum_eq_zero
  intro i _
  apply Finset.sum_eq_zero
  intro j _
  by_cases hij : i.val < j.val
  · have hn : p.vertex i ≠ p.vertex j := by
      intro he
      have := congrArg Fin.val (p.distinct i j he)
      omega
    simp [pairDefect,hij,hn,(p.induced i j hij)]
  · simp [pairDefect,hij]

theorem zero_energy_iff_snake {m : Nat} (f : Fin (m+1) → Vertex)
    (walk : ∀ i j, i.val+1 = j.val → Adj (f i) (f j)) :
    energy f = 0 ↔ ∃ p : Snake m, p.vertex = f := by
  constructor
  · intro hz
    exact ⟨snakeOfZeroEnergy f walk hz,rfl⟩
  · rintro ⟨p,rfl⟩
    exact snake_energy_zero p

#print axioms snakeOfZeroEnergy
#print axioms snake_energy_zero
#print axioms zero_energy_iff_snake
end Snake9.DefectConstruction
