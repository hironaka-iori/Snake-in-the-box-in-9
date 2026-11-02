import BalancedGraphChecks
import DefinedProofGraph

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Snake9.Potential99
open Snake9.Boxes88 Snake9.Shared89 Snake9.DefinedGraph92 Snake9.Batch92 Snake9.Certificate88

def evalBalanced : Nat → List Nat → Bool
  | node, [] => node == 1
  | node, symbol :: rest => evalBalanced (advanceBalanced node symbol) rest

theorem evalBalanced_eq (node : Nat) (symbols : List Nat) :
    evalBalanced node symbols = diagramEval retainedDiagram node symbols := by
  induction symbols generalizing node with
  | nil => rfl
  | cons symbol rest ih =>
    simp only [evalBalanced, diagramEval, advanceBalanced_eq, ih]

def fastKeep (di q code : Nat) : Bool :=
  match savedBlockClass (75*di+q) with
  | none => false
  | some cls => evalBalanced (recordedClassRoot cls) (digits code)

theorem fastKeep_eq (di q code : Nat) :
    fastKeep di q code = diagramKeep retainedDiagram di q code := by
  unfold fastKeep diagramKeep
  cases h : savedBlockClass (75*di+q)
  · rfl
  · exact evalBalanced_eq _ _

#print axioms evalBalanced_eq
#print axioms fastKeep_eq
end Snake9.Potential99
