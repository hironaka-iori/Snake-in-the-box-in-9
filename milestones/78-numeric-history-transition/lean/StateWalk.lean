import NumericTransition
import CountGeometry
import CountStateCode

namespace Snake9.GraphWalk78
open Snake9.Direction77 Snake9.History78 Snake9.CountGeometry78
open Snake9.GraphInterpretation75

def fiveCode {m : Nat} (p : Snake m) (r : Nat) : Nat :=
  encodeCounts [truncatedCount p (r+3), truncatedCount p (r+4),
    truncatedCount p (r+5), truncatedCount p (r+6), truncatedCount p (r+7)] 0

def sixCode {m : Nat} (p : Snake m) (r : Nat) : Nat :=
  encodeCounts [truncatedCount p (r+3), truncatedCount p (r+4),
    truncatedCount p (r+5), truncatedCount p (r+6), truncatedCount p (r+7),
    truncatedCount p (r+8)] 0

theorem fiveCode_lt {m : Nat} (p : Snake m) (r : Nat) (hr : r+8 ≤ m) :
    fiveCode p r < 7776 := by
  exact five_count_code _ _ _ _ _
    (truncatedCount_range p _ (by omega)) (truncatedCount_range p _ (by omega))
    (truncatedCount_range p _ (by omega)) (truncatedCount_range p _ (by omega))
    (truncatedCount_range p _ (by omega))

theorem sixCode_spec {m : Nat} (p : Snake m) (r : Nat) (hr : r+9 ≤ m) :
    sixCode p r < 46656 ∧ sixCode p r / 6 = fiveCode p r ∧
    sixCode p r % 7776 = fiveCode p (r+1) ∧
    sixCode p r % 6 + 1 = truncatedCount p (r+8) := by
  have h := six_count_code (truncatedCount p (r+3)) (truncatedCount p (r+4))
    (truncatedCount p (r+5)) (truncatedCount p (r+6))
    (truncatedCount p (r+7)) (truncatedCount p (r+8))
    (truncatedCount_range p _ (by omega)) (truncatedCount_range p _ (by omega))
    (truncatedCount_range p _ (by omega)) (truncatedCount_range p _ (by omega))
    (truncatedCount_range p _ (by omega)) (truncatedCount_range p _ (by omega))
  simpa only [fiveCode, sixCode, Nat.add_assoc, Nat.reduceAdd] using h

def actualState {m : Nat} (p : Snake m) (r : Nat) : Nat :=
  stateCode (shapeId p r) (actualHistory p r) (fiveCode p r)

theorem actualState_lt {m : Nat} (p : Snake m) (r : Nat) (hr : r+8 ≤ m) :
    actualState p r < 1601856 :=
  stateCode_lt _ _ _ (shapeId_lt p r hr) (actual_history_lt p r) (fiveCode_lt p r hr)

def edgeSource (q direction code : Nat) : Nat :=
  stateCode (sourceId direction) q (code / 6)

def edgeTarget (q direction code : Nat) : Nat :=
  stateCode (targetId direction) (builderNext q direction) (code % 7776)

theorem actual_source_state {m : Nat} (p : Snake m) (r : Nat) (hr : r+9 ≤ m) :
    edgeSource (actualHistory p r) (directionId p r) (sixCode p r) = actualState p r := by
  unfold edgeSource actualState
  rw [source_id_exact p r hr, (sixCode_spec p r hr).2.1]

theorem actual_target_state {m : Nat} (p : Snake m) (r : Nat) (hr : r+9 ≤ m) :
    edgeTarget (actualHistory p r) (directionId p r) (sixCode p r) = actualState p (r+1) := by
  unfold edgeTarget actualState
  rw [target_id_exact p r hr, actual_history_update p r, (sixCode_spec p r hr).2.2.1]

theorem consecutive_endpoints {m : Nat} (p : Snake m) (r : Nat) (hr : r+10 ≤ m) :
    edgeTarget (actualHistory p r) (directionId p r) (sixCode p r) =
    edgeSource (actualHistory p (r+1)) (directionId p (r+1)) (sixCode p (r+1)) := by
  rw [actual_target_state p r (by omega), actual_source_state p (r+1) (by omega)]

def stateSequence {m : Nat} (p : Snake m) (i : Fin (m-7)) : Fin 1601856 :=
  ⟨actualState p i.val, actualState_lt p i.val (by have h := i.isLt; omega)⟩

theorem encoded_actual_step {m : Nat} (p : Snake m) (i : Fin (m-8)) :
    edgeSource (actualHistory p i.val) (directionId p i.val) (sixCode p i.val) =
      (stateSequence p ⟨i.val, by have h := i.isLt; omega⟩).val ∧
    edgeTarget (actualHistory p i.val) (directionId p i.val) (sixCode p i.val) =
      (stateSequence p ⟨i.val+1, by have h := i.isLt; omega⟩).val := by
  have hr : i.val+9 ≤ m := by have h := i.isLt; omega
  exact ⟨actual_source_state p i.val hr, actual_target_state p i.val hr⟩

theorem history_filters {m : Nat} (p : Snake m) (r : Nat) (hr : r+9 ≤ m) :
    (actualHistory p r = 0 ∨
      recordedCompatible.getD (actualHistory p r) 0 = sourceId (directionId p r)) ∧
    (builderNext (actualHistory p r) (directionId p r) = 0 ∨
      recordedCompatible.getD (builderNext (actualHistory p r) (directionId p r)) 0 =
        targetId (directionId p r)) := by
  constructor
  · by_cases h : actualHistory p r = 0
    · exact Or.inl h
    · exact Or.inr (actual_source_history_filter p r hr h)
  · by_cases h : builderNext (actualHistory p r) (directionId p r) = 0
    · exact Or.inl h
    · exact Or.inr (builder_target_shape p r hr h)

#print axioms fiveCode_lt
#print axioms sixCode_spec
#print axioms actualState_lt
#print axioms actual_source_state
#print axioms actual_target_state
#print axioms consecutive_endpoints
#print axioms encoded_actual_step
#print axioms history_filters
end Snake9.GraphWalk78
