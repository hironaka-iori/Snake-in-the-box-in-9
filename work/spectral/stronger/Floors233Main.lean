/-
`floors233` discharges the premise `Floors233` of `upper_233_of_refuted6SB233` with main's
theorems, and `upper_233_of_certs6SB233` is the 233 chain whose only premises are the
certificate obligations `AllRefuted6SB233` and `AllRefutedShare6SB233`.

The three milestone-73 floors are restated here with main's two-line proofs
(`Snake9.CatalogueIntegration73.canonical7300/7304/7306`, `CombinedCatalogue.lean`), so the
build needs the three case certificates `Share73xx.Reversal` and `CanonicalShareAdapter`, but
not the rest of `CombinedCatalogue` (case 7305, coverage, dispatch, `CountFreeTarget`).

Build: main's 1,042 floor modules are fetched from origin/main by blob sha and compiled on
this branch (see `milestones/33-233-lean/FLOORS.md`, "Port run"); then
`chain_audit.py --target Floors233Main --extra-lean-path <port build dir>` compiles this module.
-/
import Floors233Bridge
import AggregateDirection6SB233
import CanonicalShareAdapter
import ShareComplete152
import ShareComplete155
import Share7300.Reversal
import Share7304.Reversal
import Share7306.Reversal

namespace Snake9.Floors233Port
open Snake9.LocalWindow Snake9.WindowAutomaton Snake9.DirectionWindow Snake9.CountFreeAdapter73

theorem canonical7300 {m : Nat} (p : Snake m) (r : Nat) (hr : r+6 ≤ m)
    (hshape : canon (dsOf p r 6) = [0, 1, 2, 0, 3, 1] ∨ canon (dsOf p r 6).reverse = [0, 1, 2, 0, 3, 1]) :
    16 ≤ ((List.range 5).map fun i => coreShare 12 p (r+i+1)).sum := by
  apply share_bound_of_either_canonical_match (K := 15) p r [0, 1, 2, 0, 3, 1] hr hshape
  exact LocalWindow.ShareWindow7300.refuted

theorem canonical7304 {m : Nat} (p : Snake m) (r : Nat) (hr : r+6 ≤ m)
    (hshape : canon (dsOf p r 6) = [0, 1, 2, 3, 0, 4] ∨ canon (dsOf p r 6).reverse = [0, 1, 2, 3, 0, 4]) :
    16 ≤ ((List.range 5).map fun i => coreShare 12 p (r+i+1)).sum := by
  apply share_bound_of_either_canonical_match (K := 15) p r [0, 1, 2, 3, 0, 4] hr hshape
  exact LocalWindow.ShareWindow7304.refuted

theorem canonical7306 {m : Nat} (p : Snake m) (r : Nat) (hr : r+6 ≤ m)
    (hshape : canon (dsOf p r 6) = [0, 1, 2, 3, 1, 4] ∨ canon (dsOf p r 6).reverse = [0, 1, 2, 3, 1, 4]) :
    16 ≤ ((List.range 5).map fun i => coreShare 12 p (r+i+1)).sum := by
  apply share_bound_of_either_canonical_match (K := 15) p r [0, 1, 2, 3, 1, 4] hr hshape
  exact LocalWindow.ShareWindow7306.refuted

theorem floors233 : DirectionWindow6S.Floors233 :=
  DirectionWindow6S.floors233_of_main Snake9.ShareTransfer152.share16 canonical7300 canonical7304
    canonical7306 Snake9.CriticalShare155.share17

/-- The 233 chain with the floors discharged: only the certificate obligations remain. -/
theorem upper_233_of_certs6SB233 (h : LocalWindow.AllRefuted6SB233)
    (hs : LocalWindow.AllRefutedShare6SB233) {m : Nat} (p : Snake m) : m ≤ 233 :=
  Snake9.upper_233_of_refuted6SB233 h hs floors233 p

#print axioms floors233
#print axioms upper_233_of_certs6SB233

end Snake9.Floors233Port
