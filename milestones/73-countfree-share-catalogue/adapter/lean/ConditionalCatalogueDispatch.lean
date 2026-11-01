import CanonicalShareAdapter
import SixShapeCoverage

/-! Conditional composition of the nine-shape catalogue. The nine local
certificate statements remain explicit premises throughout the dispatch. -/
namespace Snake9.CountFreeAdapter73
open Snake9.LocalWindow Snake9.WindowAutomaton Snake9.DirectionWindow
open Snake9.CountFreeCoverage73

def selectedCap (cs : List Nat) : Nat :=
  if cs = [0,1,2,0,3,4] then 19
  else if cs = [0,1,2,3,1,0] then 11 else 15

/-- Prefer the forward representative, and use canonical reversal otherwise. -/
def selectedShape (ds : List Nat) : List Nat :=
  if canon ds ∈ representatives then canon ds else canon ds.reverse

def windowLower {m : Nat} (p : Snake m) (r : Nat) : Nat :=
  selectedCap (selectedShape (dsOf p r 6)) + 1

theorem selectedCap_ge11 (cs : List Nat) : 11 ≤ selectedCap cs := by
  unfold selectedCap
  split_ifs <;> omega

theorem windowLower_ge12 {m : Nat} (p : Snake m) (r : Nat) :
    12 ≤ windowLower p r := by
  have h := selectedCap_ge11 (selectedShape (dsOf p r 6))
  unfold windowLower
  omega

theorem selectedShape_mem_and_match {m : Nat} (p : Snake m) (r : Nat)
    (hr : r+6 ≤ m) :
    selectedShape (dsOf p r 6) ∈ representatives ∧
      (canon (dsOf p r 6) = selectedShape (dsOf p r 6) ∨
        canon (dsOf p r 6).reverse = selectedShape (dsOf p r 6)) := by
  have hc := snake_window_coverage p r hr
  rw [blockList_eq_dsOf p r 6 hr] at hc
  by_cases h : canon (dsOf p r 6) ∈ representatives
  · simp [selectedShape, h]
  · simpa [selectedShape, h] using hc.resolve_left h

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

theorem representative_refutation (cs : List Nat) (hc : cs ∈ representatives) :
    RefutedShare (winOf cs) broadBounds 12 (selectedCap cs) := by
  simp only [representatives, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa [selectedCap] using h012031
  · simpa [selectedCap] using h012032
  · simpa [selectedCap] using h012034
  · simpa [selectedCap] using h012301
  · simpa [selectedCap] using h012304
  · simpa [selectedCap] using h012310
  · simpa [selectedCap] using h012314
  · simpa [selectedCap] using h012340
  · simpa [selectedCap] using h012345

/-- The catalogue lookup lower bound, conditional on all nine displayed local
certificates. No history-graph interpretation is part of this statement. -/
theorem catalogue_share_bound {m : Nat} (p : Snake m) (r : Nat) (hr : r+6 ≤ m) :
    windowLower p r ≤ ((List.range 5).map fun i => coreShare 12 p (r+i+1)).sum := by
  obtain ⟨hc, hshape⟩ := selectedShape_mem_and_match p r hr
  have href := representative_refutation h012031 h012032 h012034 h012301 h012304
    h012310 h012314 h012340 h012345 _ hc
  exact share_bound_of_either_canonical_match p r _ hr hshape href

theorem catalogue_share_ge12 {m : Nat} (p : Snake m) (r : Nat) (hr : r+6 ≤ m) :
    12 ≤ ((List.range 5).map fun i => coreShare 12 p (r+i+1)).sum := by
  exact le_trans (windowLower_ge12 p r)
    (catalogue_share_bound h012031 h012032 h012034 h012301 h012304
      h012310 h012314 h012340 h012345 p r hr)
end Certificates

#check @catalogue_share_bound
#check @catalogue_share_ge12
#print axioms selectedCap_ge11
#print axioms windowLower_ge12
#print axioms selectedShape_mem_and_match
#print axioms representative_refutation
#print axioms catalogue_share_bound
#print axioms catalogue_share_ge12
end Snake9.CountFreeAdapter73
