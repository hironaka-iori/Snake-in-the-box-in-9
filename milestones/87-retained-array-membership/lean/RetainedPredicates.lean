import ReferenceUnion
import ShortRetention
import HistoryExclusions
import IntervalCatalogue

/-! Actual-snake retention under the four checked predicate families.
This module does not identify an entry of a numerical graph array. -/
namespace Snake9.Retained87
open Snake9.LocalWindow Snake9.WindowAutomaton Snake9.DirectionWindow
open Snake9.Direction77 Snake9.History78 Snake9.GraphWalk78
open Snake9.Guards79 Snake9.ShortRules81 Snake9.History84 Snake9.Reference85
set_option maxHeartbeats 2000000

def ActualRanges {m : Nat} (p : Snake m) (r : Nat) : Prop :=
  actualHistory p r < 75 ∧ directionId p r < 505 ∧ sixCode p r < 46656

def ActualHistoryCompatibility {m : Nat} (p : Snake m) (r : Nat) : Prop :=
  (actualHistory p r = 0 ∨
    recordedCompatible.getD (actualHistory p r) 0 = sourceId (directionId p r)) ∧
  (builderNext (actualHistory p r) (directionId p r) = 0 ∨
    recordedCompatible.getD (builderNext (actualHistory p r) (directionId p r)) 0 =
      targetId (directionId p r))

def ActualReferenceFilters {m : Nat} (p : Snake m) (r : Nat) : Prop :=
  ∀ k ∈ referenceKeys, ∀ s : Nat, s+k.2.length ≤ 6 →
    ¬ forwardHit p r s k ∧ ¬ reverseHit p r s k

def ActualShortFilters {m : Nat} (p : Snake m) (r : Nat) : Prop :=
  ∀ rule ∈ shortRules, ∀ offset : Nat, ∀ reverse : Bool,
    offset+rule.1.length ≤ 9 →
    (∀ j ∈ rule.2.positions, 3 ≤ offset+orientedPosition rule.1.length reverse j ∧
      offset+orientedPosition rule.1.length reverse j ≤ 8) →
    canon (if reverse then
      (((canon (dsOf p r 9)).drop offset).take rule.1.length).reverse
      else ((canon (dsOf p r 9)).drop offset).take rule.1.length) = rule.1 →
    ¬ encodedBad rule.2 (fun j => digit (sixCode p r)
      (offset+orientedPosition rule.1.length reverse j-3))

def ActualHistoryFilters {m : Nat} (p : Snake m) (r : Nat) : Prop :=
  ∀ rule ∈ historyRules,
    ¬ builderHistoryHit (actualHistory p r) (directionId p r) (sixCode p r) rule

def ActualIntervalFilters {m : Nat} (p : Snake m) (r : Nat) : Prop :=
  ∀ key ∈ intervalKeys72, ∀ s : Nat, s ≤ 2 →
    (canon (((canon (dsOf p r 9)).drop (s+2)).take 5) = key.1 →
      ¬ intervalHit (sixCode p r) s 4 false key.2) ∧
    (canon ((((canon (dsOf p r 9)).drop (s+2)).take 5).reverse) = key.1 →
      ¬ intervalHit (sixCode p r) s 4 true key.2)

/-- Semantic predicate retention and coding prerequisites, with every test quantified.
Equality with the executable builder's numeric keep predicate is separate. -/
def ActualStepRetained {m : Nat} (p : Snake m) (r : Nat) : Prop :=
  ActualRanges p r ∧ ActualHistoryCompatibility p r ∧
    ActualReferenceFilters p r ∧ ActualShortFilters p r ∧
    ActualHistoryFilters p r ∧ ActualIntervalFilters p r

theorem actual_range_compatible {m : Nat} (p : Snake m) (r : Nat) (hr : r+9 ≤ m) :
    ActualRanges p r ∧ ActualHistoryCompatibility p r := by
  exact ⟨⟨actual_history_lt p r, directionId_lt p r hr, (sixCode_spec p r hr).1⟩,
    history_filters p r hr⟩

theorem actual_nonreference_filters {m : Nat} (p : Snake m) (r : Nat)
    (hr : r+9 ≤ m) :
    ActualShortFilters p r ∧ ActualHistoryFilters p r ∧ ActualIntervalFilters p r := by
  refine ⟨all_short_rules_retained p r hr, actual_builder_history_retained p r hr, ?_⟩
  intro key hk s hs
  exact ⟨interval_forward_retention p r s hr hs key hk,
    interval_reverse_retention p r s hr hs key hk⟩

theorem actual_step_retained (h235 : AllRefuted6K235) (h236 : AllRefuted236)
    {m : Nat} (p : Snake m) (r : Nat) (hr : r+9 ≤ m) : ActualStepRetained p r := by
  obtain ⟨hrange,hcompat⟩ := actual_range_compatible p r hr
  obtain ⟨hshort,hhistory,hinterval⟩ := actual_nonreference_filters p r hr
  refine ⟨hrange,hcompat,?_,hshort,hhistory,hinterval⟩
  intro k hk s hs
  exact concrete_reference_retained h235 h236 p r hr k hk s hs

theorem actual_retained_step_endpoints (h235 : AllRefuted6K235) (h236 : AllRefuted236)
    {m : Nat} (p : Snake m) (r : Nat) (hr : r+9 ≤ m) :
    ActualStepRetained p r ∧
    edgeSource (actualHistory p r) (directionId p r) (sixCode p r) = actualState p r ∧
    edgeTarget (actualHistory p r) (directionId p r) (sixCode p r) = actualState p (r+1) :=
  ⟨actual_step_retained h235 h236 p r hr,
    actual_source_state p r hr, actual_target_state p r hr⟩

#print axioms actual_range_compatible
#print axioms actual_nonreference_filters
#print axioms actual_step_retained
#print axioms actual_retained_step_endpoints
end Snake9.Retained87
