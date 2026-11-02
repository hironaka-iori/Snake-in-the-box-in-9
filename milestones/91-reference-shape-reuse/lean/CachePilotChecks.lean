import CachePilotData
import WitnessTablesChecks
import Balanced001Checks

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Shape91
open Snake9.Witness90 Snake9.Boxes88 Snake9.Shared89 Snake9.Certificate88 Snake9.Retained87

theorem pilot_shapes_valid :
    (List.range pilotShapeCount).all (fun i => shapeValid directionsAt (pilotShapeAt i)) = true := by
  decide +kernel

theorem pilot_shape_at_valid (i : Nat) (hi : i < pilotShapeCount) :
    shapeValid directionsAt (pilotShapeAt i) = true :=
  List.all_eq_true.mp pilot_shapes_valid i (List.mem_range.mpr hi)

def pilotCountsValid (ws : List Witness) : Bool :=
  entriesBoxCountsAt referencesAt (boxes001.zip ws)

theorem pilot_count_lists_valid : pilotCountLists.all pilotCountsValid = true := by
  decide +kernel

def cachedPilotJobValid (job : Nat × List Witness) : Bool :=
  decide (job.2.length = boxes001.length) &&
    (entriesHistoryFree (boxes001.zip job.2) &&
      (decide (job.2 ∈ pilotCountLists) &&
        entriesCachedCompatibility directionsAt referencesAt 1378 pilotShapeAt pilotShapeCount
          0 job.1 (boxes001.zip job.2) (pilotIndices job.1)))

theorem pilot_cached_jobs_valid : class001Jobs.all cachedPilotJobValid = true := by
  decide +kernel

/-- The same concrete membership conclusion as the unfactored six-job pilot. -/
theorem class001_cached_numeric_membership (di : Nat) (ws : List Witness)
    (hm : (di,ws) ∈ class001Jobs) (q code : Nat) (hq : q < 75)
    (hc : code < 46656) (hkeep : numericKeep q di code = true) :
    diagramEval retainedDiagram root001 (digits code) = true := by
  have ht := List.all_eq_true.mp pilot_cached_jobs_valid (di,ws) hm
  change (decide (ws.length = boxes001.length) &&
    (entriesHistoryFree (boxes001.zip ws) &&
      (decide (ws ∈ pilotCountLists) &&
        entriesCachedCompatibility directionsAt referencesAt 1378 pilotShapeAt pilotShapeCount
          0 di (boxes001.zip ws) (pilotIndices di)))) = true at ht
  have hlen := of_decide_eq_true (Bool.and_eq_true_iff.mp ht).1
  have hp := Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp ht).2
  have hmapped := Bool.and_eq_true_iff.mp hp.2
  have hmember : ws ∈ pilotCountLists := of_decide_eq_true hmapped.1
  have hb := List.all_eq_true.mp pilot_count_lists_valid ws hmember
  change entriesBoxCountsAt referencesAt (boxes001.zip ws) = true at hb
  have hvFast := entries_valid_of_cache directionsAt referencesAt 1378 pilotShapeAt pilotShapeCount
    pilot_shape_at_valid 0 di (boxes001.zip ws) (pilotIndices di) hmapped.2 hb
  have hv : entriesValid 0 di (boxes001.zip ws) = true := by
    simpa only [balanced_entries_eq] using hvFast
  exact history_free_shared_numeric_keep_implies_diagram 0 q di code retainedDiagram root001
    boxes001 ws tree001 hlen hp.1 hq hv originalCover001 hc hkeep

#print axioms pilot_shapes_valid
#print axioms pilot_shape_at_valid
#print axioms pilot_count_lists_valid
#print axioms pilot_cached_jobs_valid
#print axioms class001_cached_numeric_membership
end Snake9.Shape91
