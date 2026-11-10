/-
The floor premise `Floors233` of the conditional 233 (`AggregateDirection6SB233`) from the five
floor theorems of origin/main, given as hypotheses.

Core Lean only.  Each hypothesis below is the statement of one theorem on origin/main
(commit 32d14f72, 9 November 2026), copied verbatim with its binder names:

* `share16`       = `Snake9.ShareTransfer152.share16`       (milestone 152, `ShareComplete152.lean`);
* `canonical7300` = `Snake9.CatalogueIntegration73.canonical7300` (milestone 73, `CombinedCatalogue.lean`);
* `canonical7304` = `Snake9.CatalogueIntegration73.canonical7304`;
* `canonical7306` = `Snake9.CatalogueIntegration73.canonical7306`;
* `share17`       = `Snake9.CriticalShare155.share17`       (milestone 155, `ShareComplete155.lean`).

The constants they mention (`Snake`, `canon`, `dsOf`, `coreShare`, `coreAlpha`) are this
branch's: main declares them in modules that are byte-identical to this branch's
`Snake9` (main's `lean-core` copy is a prefix of this branch's file), `WindowAutomatonDefs`,
`DirectionWindowBridge` (main's `lean-core` copy is a subset), `LocalWindowBridge` and
`LocalWindowShareBridge` (see `milestones/33-233-lean/FLOORS.md`).  So once main's modules are
compiled against this branch's `.olean` files, main's theorems are terms of exactly these
hypothesis types, and `floors233_of_main` turns them into `Floors233`; the template
`milestones/33-233-lean/lean/Floors233Main.lean` does that.  The proof here is the anonymous
constructor: the hypothesis types are `ShareFloor16 shape` and `ShareFloor17` up to delta
reduction.
-/
import DirectionWindowBridge6S

namespace Snake9.DirectionWindow6S
open Snake9 Snake9.LocalWindow Snake9.WindowAutomaton Snake9.DirectionWindow

set_option linter.unusedVariables false in
theorem floors233_of_main
    (share16 : ∀ {m : Nat} (p : Snake m) (r : Nat) (hr : r+6 ≤ m)
      (hshape : canon (dsOf p r 6) = [0,1,2,0,3,2] ∨
        canon (dsOf p r 6).reverse = [0,1,2,0,3,2]),
      16 ≤ ((List.range 5).map fun i => coreShare 12 p (r+i+1)).sum)
    (canonical7300 : ∀ {m : Nat} (p : Snake m) (r : Nat) (hr : r+6 ≤ m)
      (hshape : canon (dsOf p r 6) = [0, 1, 2, 0, 3, 1] ∨ canon (dsOf p r 6).reverse = [0, 1, 2, 0, 3, 1]),
      16 ≤ ((List.range 5).map fun i => coreShare 12 p (r+i+1)).sum)
    (canonical7304 : ∀ {m : Nat} (p : Snake m) (r : Nat) (hr : r+6 ≤ m)
      (hshape : canon (dsOf p r 6) = [0, 1, 2, 3, 0, 4] ∨ canon (dsOf p r 6).reverse = [0, 1, 2, 3, 0, 4]),
      16 ≤ ((List.range 5).map fun i => coreShare 12 p (r+i+1)).sum)
    (canonical7306 : ∀ {m : Nat} (p : Snake m) (r : Nat) (hr : r+6 ≤ m)
      (hshape : canon (dsOf p r 6) = [0, 1, 2, 3, 1, 4] ∨ canon (dsOf p r 6).reverse = [0, 1, 2, 3, 1, 4]),
      16 ≤ ((List.range 5).map fun i => coreShare 12 p (r+i+1)).sum)
    (share17 : ∀ {m : Nat} (p : Snake m) (r : Nat) (hr : r+6 ≤ m)
      (hcase :
        (canon (dsOf p r 6) = [0,1,2,0,3,2] ∧
          coreAlpha p (r+1) = 4 ∧ coreAlpha p (r+2) ≤ 4 ∧
          coreAlpha p (r+3) = 4 ∧ coreAlpha p (r+4) ≤ 5 ∧
          coreAlpha p (r+5) = 3) ∨
        (canon (dsOf p r 6).reverse = [0,1,2,0,3,2] ∧
          coreAlpha p (r+1) = 3 ∧ coreAlpha p (r+2) ≤ 5 ∧
          coreAlpha p (r+3) = 4 ∧ coreAlpha p (r+4) ≤ 4 ∧
          coreAlpha p (r+5) = 4)),
      17 ≤ ((List.range 5).map fun i => coreShare 12 p (r+i+1)).sum) :
    Floors233 :=
  ⟨share16, canonical7300, canonical7304, canonical7306, share17⟩

/-- The converse: `Floors233` is no stronger than main's five theorems. -/
theorem floors233_fields (h : Floors233) :
    ShareFloor16 [0,1,2,0,3,2] ∧ ShareFloor16 [0,1,2,0,3,1] ∧ ShareFloor16 [0,1,2,3,0,4] ∧
      ShareFloor16 [0,1,2,3,1,4] ∧ ShareFloor17 :=
  ⟨h.f012032, h.f012031, h.f012304, h.f012314, h.f155⟩

#print axioms floors233_of_main
#print axioms floors233_fields

end Snake9.DirectionWindow6S
