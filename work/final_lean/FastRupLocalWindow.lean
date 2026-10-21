import WinCNF
import LocalWindowModel

/-! Exact compatibility of the two Boolean CNF semantics.
The conventions differ only at literal zero: complementing assignment bit zero
handles this too, so no nonzero-literal premise is needed by the transport.
-/
namespace Snake9.LocalWindow

def adjustZero (tau : Nat → Bool) (n : Nat) : Bool :=
  if n = 0 then !tau 0 else tau n

theorem litSat_adjustZero (tau : Nat → Bool) :
    WinCNF.litSat (adjustZero tau) = litTrue tau := by
  funext l
  cases l with
  | ofNat n =>
    cases n with
    | zero => simp [WinCNF.litSat, adjustZero, litTrue]
    | succ n => simp [WinCNF.litSat, adjustZero, litTrue]
  | negSucc n =>
    simp [WinCNF.litSat, adjustZero, litTrue]
    rfl

theorem unsat_of_fastRup {F : List (List Int)} (h : WinCNF.unsat F) : Unsat F := by
  intro tau
  cases hs : cnfTrue tau F
  · rfl
  · exfalso
    apply h (adjustZero tau)
    intro c hc
    have ht := List.all_eq_true.mp hs c hc
    simpa only [WinCNF.clauseSat, litSat_adjustZero, clauseTrue] using ht

#print axioms unsat_of_fastRup
end Snake9.LocalWindow
