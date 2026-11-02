import ConditionalCatalogueDispatch
import WindowStateShift

namespace Snake9.GraphInterpretation75
open Snake9.LocalWindow Snake9.WindowAutomaton Snake9.DirectionWindow
open Snake9.CountFreeCoverage73 Snake9.CountFreeAdapter73
open Snake9.GraphInterpretation74

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Lexicographic comparison of natural-number lists, including equality. -/
def lexLE : List Nat → List Nat → Bool
  | [], _ => true
  | _ :: _, [] => false
  | x :: xs, y :: ys => if x = y then lexLE xs ys else decide (x < y)

/-- The graph builder chooses the smaller canonical orientation. -/
def graphShape (ds : List Nat) : List Nat :=
  let f := canon ds
  let b := canon ds.reverse
  if lexLE f b then f else b

theorem canon_idempotent (ds : List Nat) : canon (canon ds) = canon ds := by
  simpa only [List.drop_zero] using canon_canon_drop ds 0

theorem canon_reverse_idempotent (ds : List Nat) :
    canon (canon ds).reverse = canon ds.reverse := by
  simpa only [List.drop_zero] using canon_canon_drop_reverse ds 0

theorem graphShape_canon (ds : List Nat) : graphShape (canon ds) = graphShape ds := by
  simp only [graphShape, canon_idempotent, canon_reverse_idempotent]

theorem selectedShape_canon (ds : List Nat) :
    selectedShape (canon ds) = selectedShape ds := by
  simp only [selectedShape, canon_idempotent, canon_reverse_idempotent]

theorem lookup_table :
    allRGS 6 0 (fun c => !inducedPattern c || decide (graphShape c = selectedShape c)) = true := by
  decide +kernel

theorem graphShape_eq_selectedShape (ds : List Nat) (hlen : ds.length = 6)
    (hind : inducedPattern ds = true) : graphShape ds = selectedShape ds := by
  have h := allRGS_spec 6 0 _ lookup_table (canon ds)
    (by simpa only [length_canon] using hlen) (canon_isRGS ds)
  have hi : inducedPattern (canon ds) = true := by simpa only [inducedPattern_canon] using hind
  have he : decide (graphShape (canon ds) = selectedShape (canon ds)) = true := by
    simpa [hi] using h
  simpa only [graphShape_canon, selectedShape_canon] using of_decide_eq_true he

/-- The graph's six-direction suffix selects exactly the actual window's rule. -/
theorem actual_suffix_lookup {m : Nat} (p : Snake m) (r : Nat)
    (hr : r+9 ≤ m) :
    graphShape ((canon (dsOf p r 9)).drop 3) = selectedShape (dsOf p (r+3) 6) := by
  have hc := canonical_nine_share_suffix p r hr
  have hi : inducedPattern (dsOf p (r+3) 6) = true := by
    rw [← blockList_eq_dsOf p (r+3) 6 (by omega)]
    exact snake_inducedPattern_block p (r+3) 6 (by omega)
  calc
    graphShape ((canon (dsOf p r 9)).drop 3) =
        graphShape (canon ((canon (dsOf p r 9)).drop 3)) := (graphShape_canon _).symm
    _ = graphShape (canon (dsOf p (r+3) 6)) := by rw [hc]
    _ = graphShape (dsOf p (r+3) 6) := graphShape_canon _
    _ = selectedShape (dsOf p (r+3) 6) :=
      graphShape_eq_selectedShape _ (by simp [length_dsOf]) hi

section Certificates
variable
  (h012031 : RefutedShare (winOf [0,1,2,0,3,1]) broadBounds 12 15)
  (h012032 : RefutedShare (winOf [0,1,2,0,3,2]) broadBounds 12 15)
  (h012034 : RefutedShare (winOf [0,1,2,0,3,4]) broadBounds 12 19)
  (h012301 : RefutedShare (winOf [0,1,2,3,0,1]) broadBounds 12 15)
  (h012304 : RefutedShare (winOf [0,1,2,3,0,4]) broadBounds 12 15)
  (h012310 : RefutedShare (winOf [0,1,2,3,1,0]) broadBounds 12 11)
  (h012314 : RefutedShare (winOf [0,1,2,3,1,4]) broadBounds 12 15)
  (h012340 : RefutedShare (winOf [0,1,2,3,4,0]) broadBounds 12 15)
  (h012345 : RefutedShare (winOf [0,1,2,3,4,5]) broadBounds 12 15)

include h012031 h012032 h012034 h012301 h012304 h012310 h012314 h012340 h012345

/-- Exact suffix lookup and centre indices; all local catalogue premises remain explicit. -/
theorem graph_catalogue_share_bound {m : Nat} (p : Snake m) (r : Nat)
    (hr : r+9 ≤ m) :
    selectedCap (graphShape ((canon (dsOf p r 9)).drop 3)) + 1 ≤
      ((List.range 5).map fun i => coreShare 12 p (r+i+4)).sum := by
  rw [actual_suffix_lookup p r hr]
  have h := catalogue_share_bound h012031 h012032 h012034 h012301 h012304
    h012310 h012314 h012340 h012345 p (r+3) (by omega)
  simpa only [windowLower, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h
end Certificates

#print axioms canon_idempotent
#print axioms canon_reverse_idempotent
#print axioms graphShape_canon
#print axioms selectedShape_canon
#print axioms lookup_table
#print axioms graphShape_eq_selectedShape
#print axioms actual_suffix_lookup
#print axioms graph_catalogue_share_bound
end Snake9.GraphInterpretation75
