import LocalWindowModel

/-!
# Canonical windows of the direction-aware certificates

The 145 window certificates behind the conditional bound 239
(`milestones/10-window-aggregate/data/direction_certificates.json`) are keyed by a
canonical direction list `ds` (a restricted growth string such as `[0, 1, 2, 0, 3]`)
and lumped counts `syms` (`sym α = min α 6`, so the symbol `6` stands for every count
from 6 to 21).  The CNF of a key is the local model of the window `winOf ds`
(`window_from_dirs` of `wincert.py`) with the count bounds `boundsOf syms`.

The key list and `AllRefuted239` are generated into `LocalWindowDirKeys.lean`.
-/

namespace Snake9.LocalWindow

/-- The vertices `v, v ⊕ e_{d₀}, v ⊕ e_{d₀} ⊕ e_{d₁}, …` of a path with directions `ds`. -/
def winGo : Nat → List Nat → List Nat
  | v, [] => [v]
  | v, d :: ds => v :: winGo (v ^^^ 2 ^ d) ds

/-- The canonical window with directions `ds`, starting at `0`. -/
def winOf (ds : List Nat) : List Nat := winGo 0 ds

/-- Count bounds of a lumped symbol: `s` itself below six, otherwise `6 ≤ α ≤ 21`. -/
def boundOf (s : Nat) : Nat × Nat := if s < 6 then (s, s) else (6, 21)

def boundsOf (syms : List Nat) : List (Nat × Nat) := syms.map boundOf

/-- Every key of the list is refuted. -/
def AllRefutedList : List (List Nat × List Nat) → Prop
  | [] => True
  | k :: ks => Refuted (winOf k.1) (boundsOf k.2) ∧ AllRefutedList ks

theorem AllRefutedList.mem : ∀ {l : List (List Nat × List Nat)}, AllRefutedList l →
    ∀ k ∈ l, Refuted (winOf k.1) (boundsOf k.2)
  | [], _, k, hk => absurd hk List.not_mem_nil
  | _ :: _, h, k, hk => by
    rcases List.mem_cons.1 hk with rfl | hk
    · exact h.1
    · exact AllRefutedList.mem h.2 k hk

end Snake9.LocalWindow
