module

/-
Lean 4.35 port of `work/spectral/stronger/Floors233Main.lean`, `floors233` part (FLOORS.md):
`Floors233` (statement unchanged, `Floors233Bridge`) proved from main's five floor theorems,
whose modules (the 1,042 fetched from origin/main at 32d14f72, ported by
lean435/floors/tools/port_floors.py) are imported privately: a module importing this one loads
only `Floors233Bridge` and its support closure, and the statement of `floors233`.
The three milestone-73 floors are restated with main's two-line proofs, as in Floors233Main.
`upper_233_of_certs6SB233` is left to the chain port (it needs `AggregateDirection6SB233`).
-/
public import Floors233Bridge
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

public theorem floors233 : DirectionWindow6S.Floors233 :=
  DirectionWindow6S.floors233_of_main Snake9.ShareTransfer152.share16 canonical7300 canonical7304
    canonical7306 Snake9.CriticalShare155.share17

#print axioms floors233

end Snake9.Floors233Port
