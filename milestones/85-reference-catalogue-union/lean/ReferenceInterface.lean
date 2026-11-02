import ReferenceRetention
import LocalWindowDirKeys6K235
import LocalWindowDirKeysR4

namespace Snake9.Reference85
open Snake9.LocalWindow Snake9.WindowAutomaton Snake9.DirectionWindow
open Snake9.Guards79 Snake9.GraphInterpretation75 Snake9.GraphWalk78
set_option maxHeartbeats 2000000

abbrev Key := List Nat × List Nat

def keyValid (k : Key) : Bool :=
  decide (2 ≤ k.2.length ∧ k.2.length ≤ 6 ∧ k.1.length = k.2.length+1) &&
    k.2.all (fun s => decide (1 ≤ s ∧ s ≤ 6))

def keyCovered (k : Key) : Bool := (dirKeys6K235 ++ dirKeysR4).contains k

theorem keyValid_spec (k : Key) (h : keyValid k = true) :
    2 ≤ k.2.length ∧ k.2.length ≤ 6 ∧ k.1.length = k.2.length+1 ∧
      ∀ s ∈ k.2, 1 ≤ s ∧ s ≤ 6 := by
  simpa only [keyValid, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, and_assoc] using h

theorem covered_key_refuted (h235 : AllRefuted6K235) (h236 : AllRefuted236)
    (k : Key) (hc : keyCovered k = true) : Refuted (winOf k.1) (boundsOf k.2) := by
  have hm : k ∈ dirKeys6K235 ++ dirKeysR4 := List.contains_iff.mp hc
  rcases List.mem_append.mp hm with h | h
  · exact AllRefutedList.mem (l := dirKeys6K235) h235 k h
  · exact AllRefutedList.mem (l := dirKeysR4) h236 k h

theorem allRefutedList_of_forall (keys : List Key)
    (h : ∀ k ∈ keys, Refuted (winOf k.1) (boundsOf k.2)) : AllRefutedList keys := by
  induction keys with
  | nil => trivial
  | cons k ks ih =>
    exact ⟨h k (by simp), ih (fun x hx => h x (by simp [hx]))⟩

theorem allRefuted_of_covered (h235 : AllRefuted6K235) (h236 : AllRefuted236)
    (keys : List Key) (hc : keys.all keyCovered = true) : AllRefutedList keys := by
  apply allRefutedList_of_forall
  intro k hk
  exact covered_key_refuted h235 h236 k (List.all_eq_true.mp hc k hk)

def forwardHit {m : Nat} (p : Snake m) (r s : Nat) (k : Key) : Prop :=
  canon (((canon (dsOf p r 9)).drop (s+2)).take (k.2.length+1)) = k.1 ∧
    sixCode p r / 6^(6-s-k.2.length) % 6^k.2.length = encodeCounts k.2 0

def reverseHit {m : Nat} (p : Snake m) (r s : Nat) (k : Key) : Prop :=
  canon ((((canon (dsOf p r 9)).drop (s+2)).take (k.2.length+1)).reverse) = k.1 ∧
    sixCode p r / 6^(6-s-k.2.length) % 6^k.2.length = encodeCounts k.2.reverse 0

theorem refuted_key_retained {m : Nat} (p : Snake m) (r s : Nat) (k : Key)
    (hr : r+9 ≤ m) (hs : s+k.2.length ≤ 6) (hv : keyValid k = true)
    (href : Refuted (winOf k.1) (boundsOf k.2)) :
    ¬ forwardHit p r s k ∧ ¬ reverseHit p r s k := by
  obtain ⟨hw, _, _, hvalid⟩ := keyValid_spec k hv
  constructor
  · intro hh
    exact encoded_forward_exclusion p r s k.2.length hr hw hs k.1 k.2 rfl hvalid href hh.1 hh.2
  · intro hh
    exact encoded_reverse_exclusion p r s k.2.length hr hw hs k.1 k.2 rfl hvalid href hh.1 hh.2

theorem covered_key_retained (h235 : AllRefuted6K235) (h236 : AllRefuted236)
    {m : Nat} (p : Snake m) (r s : Nat) (k : Key)
    (hr : r+9 ≤ m) (hs : s+k.2.length ≤ 6)
    (hv : keyValid k = true) (hc : keyCovered k = true) :
    ¬ forwardHit p r s k ∧ ¬ reverseHit p r s k :=
  refuted_key_retained p r s k hr hs hv (covered_key_refuted h235 h236 k hc)

theorem all_reference_guards_retained (h235 : AllRefuted6K235) (h236 : AllRefuted236)
    (keys : List Key) (hv : keys.all keyValid = true) (hc : keys.all keyCovered = true)
    {m : Nat} (p : Snake m) (r : Nat) (hr : r+9 ≤ m)
    (k : Key) (hk : k ∈ keys) (s : Nat) (hs : s+k.2.length ≤ 6) :
    ¬ forwardHit p r s k ∧ ¬ reverseHit p r s k :=
  covered_key_retained h235 h236 p r s k hr hs
    (List.all_eq_true.mp hv k hk) (List.all_eq_true.mp hc k hk)

#print axioms keyValid_spec
#print axioms covered_key_refuted
#print axioms allRefutedList_of_forall
#print axioms allRefuted_of_covered
#print axioms refuted_key_retained
#print axioms covered_key_retained
#print axioms all_reference_guards_retained
end Snake9.Reference85
