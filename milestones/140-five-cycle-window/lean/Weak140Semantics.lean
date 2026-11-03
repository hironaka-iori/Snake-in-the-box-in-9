import LocalWindowSat.CycleBase140

namespace Snake9.Weak140
open Snake9.LocalWindow Snake9.LocalWindow.Tags
open Snake9.LocalWindow.CycleBase140 (window meaning tags raw cnf)
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

def bounds : List (Nat × Nat) := [(3,3),(0,5),(4,4),(0,5),(3,3)]

def ctrs : List Ctr :=
  (Snake9.LocalWindow.CycleBase140.ctrs.set 4 dfltCtr).set 8 dfltCtr

theorem check : checkAll meaning ctrs window bounds tags raw = true := by
  decide +kernel

theorem sat : ∀ S E : Nat → Bool,
    Axioms S E window (centresOf window bounds) → ∃ τ, cnfTrue τ cnf = true :=
  fun S E h => ⟨tau S E meaning ctrs, sound meaning ctrs window bounds tags raw check S E h⟩

#print axioms check
#print axioms sat
end Snake9.Weak140
