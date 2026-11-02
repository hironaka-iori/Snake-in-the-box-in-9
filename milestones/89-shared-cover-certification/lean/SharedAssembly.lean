import ContextTransport

namespace Snake9.Shared89
open Snake9.Boxes88 Snake9.Retained87

theorem zip_boxes (boxes : List Box) (ws : List Witness)
    (hlen : ws.length = boxes.length) :
    (boxes.zip ws).map Prod.fst = boxes := by
  exact List.map_fst_zip (by omega)

/-- Geometry is supplied once; a same-length witness list supplies provenance
for each box in that order. Both finite checks remain explicit. -/
theorem shared_numeric_keep_implies_diagram (q di code : Nat) (g : Diagram) (node : Nat)
    (boxes : List Box) (ws : List Witness) (certificate : CoverTree)
    (hlen : ws.length = boxes.length)
    (hv : entriesValid q di (boxes.zip ws) = true)
    (hcover : checkCover g boxes 6 [] node certificate = true)
    (hc : code < 46656) (hkeep : numericKeep q di code = true) :
    diagramEval g node (digits code) = true := by
  exact numeric_keep_implies_diagram q di code g node (boxes.zip ws) certificate hc hv
    (by simpa only [zip_boxes boxes ws hlen] using hcover) hkeep

/-- A geometric witness list checked at q0 can be reused at any bounded q,
with the same geometry and cover certificate. -/
theorem history_free_shared_numeric_keep_implies_diagram
    (q0 q di code : Nat) (g : Diagram) (node : Nat)
    (boxes : List Box) (ws : List Witness) (certificate : CoverTree)
    (hlen : ws.length = boxes.length)
    (hfree : entriesHistoryFree (boxes.zip ws) = true) (hq : q < 75)
    (hv0 : entriesValid q0 di (boxes.zip ws) = true)
    (hcover : checkCover g boxes 6 [] node certificate = true)
    (hc : code < 46656) (hkeep : numericKeep q di code = true) :
    diagramEval g node (digits code) = true := by
  exact shared_numeric_keep_implies_diagram q di code g node boxes ws certificate hlen
    (entries_valid_transport q0 q di (boxes.zip ws) hfree hq hv0) hcover hc hkeep

/-- Preserve the materialized order when the history witness is the head entry. -/
theorem base_after_history_valid (q di : Nat) (base : List (Box × Witness))
    (b : Box) (ki : Nat) (hq : q < 75)
    (hfree : entriesHistoryFree base = true)
    (hb : entriesValid 0 di base = true)
    (hh : boxWitnessValid q di b (.history ki) = true) :
    entriesValid q di ((b, .history ki) :: base) = true := by
  change (boxWitnessValid q di b (.history ki) && entriesValid q di base) = true
  exact Bool.and_eq_true_iff.mpr
    ⟨hh,entries_valid_transport 0 q di base hfree hq hb⟩

#print axioms zip_boxes
#print axioms shared_numeric_keep_implies_diagram
#print axioms history_free_shared_numeric_keep_implies_diagram
#print axioms base_after_history_valid
end Snake9.Shared89
