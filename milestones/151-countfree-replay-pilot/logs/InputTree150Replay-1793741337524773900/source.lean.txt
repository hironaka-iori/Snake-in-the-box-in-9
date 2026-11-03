import LratFast150Replay

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace Snake9.ReplayInput150

open Snake9.LocalWindow
open Snake9.Lrat150Replay (Tree TreeTrue rawMask rawMask_true)
open Snake9.LratFast150Replay (perf perf_true)

inductive InputTree where
  | empty : InputTree
  | tautology (depth base : Nat) : InputTree
  | node (key : Nat) (clause : List Nat) (left right : InputTree) : InputTree

noncomputable def InputTree.build : InputTree → Tree
  | .empty => .nil
  | .tautology d b => perf d b
  | .node k c left right => .node k (rawMask c) left.build right.build

def InputTree.clauses : InputTree → List (List Nat)
  | .empty => []
  | .tautology _ _ => []
  | .node _ c left right => c :: (left.clauses ++ right.clauses)

theorem InputTree.build_true (τ : Nat → Bool) (t : InputTree)
    (h : (t.clauses.map (·.map decodeLit)).all (clauseTrue τ) = true) :
    TreeTrue τ t.build := by
  induction t with
  | empty => exact .nil
  | tautology d b => exact perf_true τ d b
  | node k c left right ihl ihr =>
    simp only [InputTree.clauses, List.map_cons, List.map_append,
      List.all_cons, List.all_append, Bool.and_eq_true] at h
    exact .node (rawMask_true τ c h.1) (ihl h.2.1) (ihr h.2.2)

theorem InputTree.start_true (τ : Nat → Bool) (t : InputTree)
    {raw : List (List Nat)} (heq : t.clauses = raw)
    (h : cnfTrue τ (raw.map (·.map decodeLit)) = true) : TreeTrue τ t.build := by
  apply t.build_true τ
  rw [heq]
  exact h

end Snake9.ReplayInput150

#print axioms Snake9.ReplayInput150.InputTree.build_true
#print axioms Snake9.ReplayInput150.InputTree.start_true
