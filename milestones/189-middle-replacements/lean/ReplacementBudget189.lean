import Std
namespace MiddleReplacement189

theorem overlapRepairBudget {V : Type} (xs : List V)
    (oldMiddle oldOuter newMiddle newOuter : V → Bool)
    (hcompat : ∀ v ∈ xs, (newMiddle v && newOuter v) = false) :
    xs.countP (fun v => oldMiddle v && oldOuter v) ≤
      xs.countP (fun v => oldMiddle v && !newMiddle v) +
      xs.countP (fun v => oldOuter v && !newOuter v) := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    have ha := hcompat a (by simp)
    have ht := ih (by intro v hv; exact hcompat v (by simp [hv]))
    simp only [List.countP_cons]
    cases hm : oldMiddle a <;> cases ho : oldOuter a <;>
      cases hn : newMiddle a <;> cases hp : newOuter a <;>
      simp_all <;> omega

theorem fixedOuterBudget {V : Type} (xs : List V)
    (oldMiddle outer newMiddle : V → Bool)
    (hcompat : ∀ v ∈ xs, (newMiddle v && outer v) = false) :
    xs.countP (fun v => oldMiddle v && outer v) ≤
      xs.countP (fun v => oldMiddle v && !newMiddle v) := by
  have h := overlapRepairBudget xs oldMiddle outer newMiddle outer hcompat
  have hz : xs.countP (fun v => outer v && !outer v)=0 := by
    induction xs with
    | nil => simp
    | cons a xs ih => cases h : outer a <;> simp_all
  omega

#print axioms overlapRepairBudget
#print axioms fixedOuterBudget
end MiddleReplacement189
