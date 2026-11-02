import Port98CombinedCatalogue
import GraphShareLookup
import ActualDirectionIds

/-!
Completed and weaker conditional count-free credits for an actual graph edge.
The five pending local refutations remain explicit. The conditional012034
credit is18, obtained from cap17, rather than the older cap19 catalogue.
-/
namespace Snake9.CountFree98
open Snake9.LocalWindow Snake9.WindowAutomaton Snake9.DirectionWindow
open Snake9.CountFreeAdapter73 Snake9.CatalogueIntegration73
open Snake9.GraphInterpretation75 Snake9.Direction77

set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

/-- Closed count-free floors; unsupported representatives contribute zero. -/
def completedFloor (cs : List Nat) : Nat :=
  if cs = [0,1,2,0,3,1] then 16
  else if cs = [0,1,2,3,0,4] then 16
  else if cs = [0,1,2,3,1,0] then 12
  else if cs = [0,1,2,3,1,4] then 16
  else if cs = [0,1,2,3,4,5] then 12
  else 0

/-- Five pending improvements, including18 on012034. -/
def conditionalFloor (cs : List Nat) : Nat :=
  if cs = [0,1,2,0,3,2] then 16
  else if cs = [0,1,2,0,3,4] then 18
  else if cs = [0,1,2,3,0,1] then 16
  else if cs = [0,1,2,3,4,0] then 16
  else if cs = [0,1,2,3,4,5] then 16
  else completedFloor cs

/-- Executable lookup on the stored nine-direction word and its last six
directions. The graph's canonical orientation is preserved exactly. -/
def completedCredit (di : Nat) : Nat :=
  completedFloor (graphShape ((extensions.getD di []).drop 3))

def conditionalCredit (di : Nat) : Nat :=
  conditionalFloor (graphShape ((extensions.getD di []).drop 3))

/-- The older completed distinct-direction certificate gives12 in either
canonical orientation, without any count-symbol premise. -/
theorem canonical_distinct_completed {m : Nat} (p : Snake m) (t : Nat)
    (ht : t+6 ≤ m)
    (hshape : canon (dsOf p t 6) = [0,1,2,3,4,5] ∨
      canon (dsOf p t 6).reverse = [0,1,2,3,4,5]) :
    12 ≤ ((List.range 5).map fun i => coreShare 12 p (t+i+1)).sum := by
  apply share_bound_of_either_canonical_match (K := 11)
    p t [0,1,2,3,4,5] ht hshape
  exact Snake9.LocalWindow.ShareWindow12.refuted

/-- The five completed entries are actual-window share bounds. -/
theorem completed_selected_bound {m : Nat} (p : Snake m) (t : Nat)
    (ht : t+6 ≤ m) :
    completedFloor (selectedShape (dsOf p t 6)) ≤
      ((List.range 5).map fun i => coreShare 12 p (t+i+1)).sum := by
  obtain ⟨_, hmatch⟩ := selectedShape_mem_and_match p t ht
  unfold completedFloor
  split_ifs with h7300 h7304 h7305 h7306 hdistinct
  · exact canonical7300 p t ht (by simpa only [h7300] using hmatch)
  · exact canonical7304 p t ht (by simpa only [h7304] using hmatch)
  · exact canonical7305 p t ht (by simpa only [h7305] using hmatch)
  · exact canonical7306 p t ht (by simpa only [h7306] using hmatch)
  · exact canonical_distinct_completed p t ht (by simpa only [hdistinct] using hmatch)
  · exact Nat.zero_le _

/-- The weaker conditional profile uses exactly the five stated refutations.
The7302 premise has cap17 and therefore supplies a floor of18. -/
theorem conditional_selected_bound
    (h7301 : RefutedShare (winOf [0,1,2,0,3,2]) broadBounds 12 15)
    (h7302 : RefutedShare (winOf [0,1,2,0,3,4]) broadBounds 12 17)
    (h7303 : RefutedShare (winOf [0,1,2,3,0,1]) broadBounds 12 15)
    (h7307 : RefutedShare (winOf [0,1,2,3,4,0]) broadBounds 12 15)
    (h7308 : RefutedShare (winOf [0,1,2,3,4,5]) broadBounds 12 15)
    {m : Nat} (p : Snake m) (t : Nat) (ht : t+6 ≤ m) :
    conditionalFloor (selectedShape (dsOf p t 6)) ≤
      ((List.range 5).map fun i => coreShare 12 p (t+i+1)).sum := by
  obtain ⟨_, hmatch⟩ := selectedShape_mem_and_match p t ht
  unfold conditionalFloor
  split_ifs with h1 h2 h3 h7 h8
  · exact share_bound_of_either_canonical_match (K := 15)
      p t [0,1,2,0,3,2] ht (by simpa only [h1] using hmatch) h7301
  · exact share_bound_of_either_canonical_match (K := 17)
      p t [0,1,2,0,3,4] ht (by simpa only [h2] using hmatch) h7302
  · exact share_bound_of_either_canonical_match (K := 15)
      p t [0,1,2,3,0,1] ht (by simpa only [h3] using hmatch) h7303
  · exact share_bound_of_either_canonical_match (K := 15)
      p t [0,1,2,3,4,0] ht (by simpa only [h7] using hmatch) h7307
  · exact share_bound_of_either_canonical_match (K := 15)
      p t [0,1,2,3,4,5] ht (by simpa only [h8] using hmatch) h7308
  · exact completed_selected_bound p t ht

/-- Closed count-free credit on the actual numeric direction key. -/
theorem actual_completed_credit {m : Nat} (p : Snake m) (r : Nat)
    (hr : r+9 ≤ m) :
    completedCredit (directionId p r) ≤
      ((List.range 5).map fun i => coreShare 12 p (r+(i+4))).sum := by
  unfold completedCredit
  rw [direction_decode p r hr, actual_suffix_lookup p r hr]
  have h := completed_selected_bound p (r+3) (by omega)
  simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h

/-- Conditional count-free credit on the actual numeric direction key.
All five local premises are retained; no count symbol is read as an exact
value, and the centres are precisely r+4 through r+8. -/
theorem actual_conditional_credit
    (h7301 : RefutedShare (winOf [0,1,2,0,3,2]) broadBounds 12 15)
    (h7302 : RefutedShare (winOf [0,1,2,0,3,4]) broadBounds 12 17)
    (h7303 : RefutedShare (winOf [0,1,2,3,0,1]) broadBounds 12 15)
    (h7307 : RefutedShare (winOf [0,1,2,3,4,0]) broadBounds 12 15)
    (h7308 : RefutedShare (winOf [0,1,2,3,4,5]) broadBounds 12 15)
    {m : Nat} (p : Snake m) (r : Nat) (hr : r+9 ≤ m) :
    conditionalCredit (directionId p r) ≤
      ((List.range 5).map fun i => coreShare 12 p (r+(i+4))).sum := by
  unfold conditionalCredit
  rw [direction_decode p r hr, actual_suffix_lookup p r hr]
  have h := conditional_selected_bound h7301 h7302 h7303 h7307 h7308
    p (r+3) (by omega)
  simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h

#print axioms canonical_distinct_completed
#print axioms completed_selected_bound
#print axioms conditional_selected_bound
#print axioms actual_completed_credit
#print axioms actual_conditional_credit
end Snake9.CountFree98
