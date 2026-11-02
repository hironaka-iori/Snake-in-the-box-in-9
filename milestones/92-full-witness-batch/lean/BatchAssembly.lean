import WitnessTablesChecks

namespace Snake9.Batch92
open Snake9.Boxes88 Snake9.Shared89 Snake9.Witness90 Snake9.Retained87

/-- The class001 job validator with its box list made explicit. -/
def baseJobValid (boxes : List Box) (job : Nat × List Witness) : Bool :=
  decide (job.2.length = boxes.length) &&
    (entriesHistoryFree (boxes.zip job.2) &&
      entriesValidAt directionsAt referencesAt 1378 0 job.1 (boxes.zip job.2))

theorem baseJobValid_spec (boxes : List Box) (di : Nat) (ws : List Witness)
    (hjob : baseJobValid boxes (di,ws) = true) :
    ws.length = boxes.length ∧ entriesHistoryFree (boxes.zip ws) = true ∧
      entriesValid 0 di (boxes.zip ws) = true := by
  have h := Bool.and_eq_true_iff.mp hjob
  have hp := Bool.and_eq_true_iff.mp h.2
  refine ⟨of_decide_eq_true h.1,hp.1,?_⟩
  simpa only [balanced_entries_eq] using hp.2

theorem base_jobs_extract (boxes : List Box) (jobs : List (Nat × List Witness))
    (hall : jobs.all (baseJobValid boxes) = true) (di : Nat) (ws : List Witness)
    (hm : (di,ws) ∈ jobs) :
    ws.length = boxes.length ∧ entriesHistoryFree (boxes.zip ws) = true ∧
      entriesValid 0 di (boxes.zip ws) = true := by
  exact baseJobValid_spec boxes di ws (List.all_eq_true.mp hall (di,ws) hm)

/-- A checked history-free base job works at every bounded history index.
The original coverage equation and numeric predicate remain explicit. -/
theorem base_job_numeric_membership (boxes : List Box) (di : Nat) (ws : List Witness)
    (hjob : baseJobValid boxes (di,ws) = true)
    (g : Diagram) (node : Nat) (certificate : CoverTree)
    (hcover : checkCover g boxes 6 [] node certificate = true)
    (q code : Nat) (hq : q < 75) (hc : code < 46656)
    (hkeep : numericKeep q di code = true) :
    diagramEval g node (digits code) = true := by
  obtain ⟨hlen,hfree,hvalid⟩ := baseJobValid_spec boxes di ws hjob
  exact history_free_shared_numeric_keep_implies_diagram 0 q di code g node boxes ws
    certificate hlen hfree hq hvalid hcover hc hkeep

/-- Restore a separately validated history witness at the head without changing
the ordered full box list or its original coverage equation. -/
theorem head_restored_numeric_membership (b : Box) (tail : List Box) (di : Nat)
    (base : List Witness) (ki : Nat) (hjob : baseJobValid tail (di,base) = true)
    (g : Diagram) (node : Nat) (certificate : CoverTree)
    (hcover : checkCover g (b :: tail) 6 [] node certificate = true)
    (q code : Nat) (hq : q < 75)
    (hhead : boxWitnessValid q di b (.history ki) = true)
    (hc : code < 46656) (hkeep : numericKeep q di code = true) :
    diagramEval g node (digits code) = true := by
  obtain ⟨hlen,hfree,hvalid⟩ := baseJobValid_spec tail di base hjob
  have hfull : entriesValid q di ((b :: tail).zip (.history ki :: base)) = true := by
    change entriesValid q di ((b,.history ki) :: (tail.zip base)) = true
    exact base_after_history_valid q di (tail.zip base) b ki hq hfree hvalid hhead
  exact shared_numeric_keep_implies_diagram q di code g node (b :: tail)
    (.history ki :: base) certificate (by simpa only [List.length_cons] using congrArg Nat.succ hlen)
    hfull hcover hc hkeep

#print axioms baseJobValid_spec
#print axioms base_jobs_extract
#print axioms base_job_numeric_membership
#print axioms head_restored_numeric_membership
end Snake9.Batch92
