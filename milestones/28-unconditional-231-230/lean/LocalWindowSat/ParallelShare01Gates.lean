import ParallelShareBoolean
import LocalWindowCnf.ParallelShare01

/-! Exact gate-clause subset of the committed Boolean pilot. Totalizer and
degree clauses still require their separate applicability proofs. -/
namespace Snake9.LocalWindow.ParallelShare01GatePilot
open Snake9.ParallelShareBoolean
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def window : List Nat := [0, 1, 3, 7, 6, 14, 12, 28]
def meanings : List (Option Formula) := [some (.sel 0), some (.sel 1), some (.sel 3), some (.sel 6), some (.sel 7), some (.sel 8), some (.sel 9), some (.sel 10), some (.sel 11), some (.sel 12), some (.sel 13), some (.sel 14), some (.sel 15), some (.sel 28), some (square 8 0 1), some (square 9 1 2), some (one (square 9 1 2) 12 10 8), some (one (square 8 0 1) 15 12 13), some (one (square 9 1 2) 14 8 10), some (one (square 8 0 1) 13 14 15), none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none, none]
def meaning (n : Nat) : Option Formula := meanings.getD (n - 1) none
def indices : List Nat := [14, 15, 16, 17, 18, 19]
noncomputable def gateCnf : List (List Int) :=
  indices.map fun i => (ParallelShare01.raw.getD i []).map decodeLit

theorem checked : gateCnf.all (checkClause 8 window meaning) = true := by decide +kernel

theorem gates_sound (S : Nat → Bool) (hw : ∀ v ∈ window, S v = true) :
    cnfTrue (assignment meaning S) gateCnf = true :=
  checkClauses_sound 8 window meaning gateCnf checked S hw

/-- Removing the empty-square alternative from the first actual clause is rejected. -/
theorem rejects_missing_empty_bit :
    checkClause 8 window meaning ((gateCnf.getD 0 []).drop 1) = false := by decide +kernel

#print axioms checked
#print axioms gates_sound
#print axioms rejects_missing_empty_bit
end Snake9.LocalWindow.ParallelShare01GatePilot
