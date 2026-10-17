import WindowGeometry

namespace Snake9.Window244
noncomputable section
local instance propDecCounter (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0

def endpointCount {m : Nat} (p : Snake m) (vs : List Vertex) : Nat :=
  (vs.filter (fun v => decide (BallClauseLogic.Endpoint p v))).length

def missingCount {m : Nat} (p : Snake m) (vs : List Vertex) : Nat :=
  (vs.filter (fun v => decide (¬ InPath p v))).length

theorem endpointCount_append {m : Nat} (p : Snake m) (vs : List Vertex) (v : Vertex) :
    endpointCount p (vs ++ [v]) = endpointCount p vs +
      (if BallClauseLogic.Endpoint p v then 1 else 0) := by
  by_cases h : BallClauseLogic.Endpoint p v <;> simp [endpointCount,h]

theorem missingCount_append {m : Nat} (p : Snake m) (vs : List Vertex) (v : Vertex) :
    missingCount p (vs ++ [v]) = missingCount p vs +
      (if ¬ InPath p v then 1 else 0) := by
  by_cases h : InPath p v <;> simp [missingCount,h]

/-- All five endpoint-counter clause families share this proof. -/
theorem endpoint_counter_clauses {m : Nat} (p : Snake m) (vs : List Vertex)
    (v : Vertex) (hn : (vs ++ [v]).Nodup) :
    (¬ BallClauseLogic.Endpoint p v ∨ 1 ≤ endpointCount p (vs ++ [v])) ∧
    (¬ (1 ≤ endpointCount p vs) ∨ 1 ≤ endpointCount p (vs ++ [v])) ∧
    (¬ (2 ≤ endpointCount p vs) ∨ 2 ≤ endpointCount p (vs ++ [v])) ∧
    (¬ BallClauseLogic.Endpoint p v ∨ ¬ (1 ≤ endpointCount p vs) ∨
      2 ≤ endpointCount p (vs ++ [v])) ∧
    (¬ BallClauseLogic.Endpoint p v ∨ ¬ (2 ≤ endpointCount p vs)) := by
  have hb := endpoint_count p (vs ++ [v]) hn
  change endpointCount p (vs ++ [v]) ≤ 2 at hb
  simp only [endpointCount_append] at hb ⊢
  by_cases h : BallClauseLogic.Endpoint p v <;> simp [h] at hb ⊢ <;> omega

/-- The exact four CNF clauses emitted for a missing-counter cell. -/
theorem missing_counter_clauses {m : Nat} (p : Snake m) (vs : List Vertex)
    (v : Vertex) (j : Nat) (hj : 0 < j) :
    (¬ (j ≤ missingCount p vs) ∨ j ≤ missingCount p (vs ++ [v])) ∧
    (¬ (¬ InPath p v) ∨ ¬ (j-1 ≤ missingCount p vs) ∨ j ≤ missingCount p (vs ++ [v])) ∧
    (¬ (j ≤ missingCount p (vs ++ [v])) ∨ j ≤ missingCount p vs ∨ ¬ InPath p v) ∧
    (¬ (j ≤ missingCount p (vs ++ [v])) ∨ j ≤ missingCount p vs ∨ j-1 ≤ missingCount p vs) := by
  apply recurrence_clauses
  rw [missingCount_append]
  by_cases h : InPath p v <;> simp only [h,not_true_eq_false,not_false_eq_true,
    if_true,if_false,true_and,false_and,or_false] <;> omega

theorem missing_exact_clauses {m : Nat} (p : Snake m) (vs : List Vertex)
    (k : Nat) (hk : missingCount p vs = k) :
    k ≤ missingCount p vs ∧ ¬ (k+1 ≤ missingCount p vs) := by omega

#print axioms endpoint_counter_clauses
#print axioms missing_counter_clauses
#print axioms missing_exact_clauses
end
end Snake9.Window244
