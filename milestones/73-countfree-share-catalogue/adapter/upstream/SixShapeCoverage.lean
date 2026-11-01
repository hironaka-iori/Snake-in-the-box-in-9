import WindowAutomatonBridge
import WindowAutomatonLemmas

/-!
Coverage of the six-transition share catalogue. First-occurrence normalization,
its transport of the induced-pattern predicate, and the actual-snake parity
bridge are inherited from the pinned normalization support. Only restricted-
growth strings are enumerated by the new finite check.
-/
namespace Snake9.CountFreeCoverage73
open Snake9.WindowAutomaton
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def representatives : List (List Nat) :=
  [[0,1,2,0,3,1], [0,1,2,0,3,2], [0,1,2,0,3,4],
   [0,1,2,3,0,1], [0,1,2,3,0,4], [0,1,2,3,1,0],
   [0,1,2,3,1,4], [0,1,2,3,4,0], [0,1,2,3,4,5]]

def represented (c : List Nat) : Bool :=
  decide (c ∈ representatives ∨ canon c.reverse ∈ representatives)

theorem catalogue_size : representatives.length = 9 ∧ representatives.Nodup := by
  decide +kernel

theorem restricted_growth_table :
    allRGS 6 0 (fun c => !inducedPattern c || represented c) = true := by
  decide +kernel

/-- The complete finite classification, under its explicit canonical and
induced-pattern hypotheses. -/
theorem canonical_coverage (c : List Nat) (hlen : c.length = 6)
    (hrgs : isRGS c 0 = true) (hind : inducedPattern c = true) :
    c ∈ representatives ∨ canon c.reverse ∈ representatives := by
  have h := allRGS_spec 6 0 _ restricted_growth_table c hlen hrgs
  have he : decide (c ∈ representatives ∨ canon c.reverse ∈ representatives) = true := by
    simpa [hind, represented] using h
  exact of_decide_eq_true he

/-- Every actual six-transition snake window has one of the listed shapes,
possibly after reversing the actual transition list and relabelling it. -/
theorem snake_window_coverage {m : Nat} (p : Snake m) (r : Nat) (hr : r+6 ≤ m) :
    canon (blockList p r 6) ∈ representatives ∨
      canon (blockList p r 6).reverse ∈ representatives := by
  have hlen : (canon (blockList p r 6)).length = 6 := by
    rw [length_canon]
    simp [blockList]
  have hind : inducedPattern (canon (blockList p r 6)) = true := by
    rw [inducedPattern_canon]
    exact snake_inducedPattern_block p r 6 hr
  have h := canonical_coverage _ hlen (canon_isRGS _) hind
  have hrev : canon (canon (blockList p r 6)).reverse = canon (blockList p r 6).reverse := by
    simpa only [List.drop_zero] using canon_canon_drop_reverse (blockList p r 6) 0
  simpa only [hrev] using h

#print axioms catalogue_size
#print axioms restricted_growth_table
#print axioms canonical_coverage
#print axioms snake_window_coverage
end Snake9.CountFreeCoverage73
