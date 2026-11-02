import Class001WitnessData
import WitnessTablesChecks
import Balanced001Checks

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Witness90
open Snake9.Boxes88 Snake9.Shared89 Snake9.Certificate88 Snake9.Retained87

def class001JobValid (job : Nat × List Witness) : Bool :=
  decide (job.2.length = boxes001.length) &&
    (entriesHistoryFree (boxes001.zip job.2) &&
      entriesValidAt directionsAt referencesAt 1378 0 job.1 (boxes001.zip job.2))

theorem class001_jobs_valid : class001Jobs.all class001JobValid = true := by
  decide +kernel

/-- Every listed direction uses the checked shared cover, for every bounded
history. The original numeric predicate, including all history guards, remains. -/
theorem class001_numeric_membership (di : Nat) (ws : List Witness)
    (hm : (di,ws) ∈ class001Jobs) (q code : Nat) (hq : q < 75)
    (hc : code < 46656) (hkeep : numericKeep q di code = true) :
    diagramEval retainedDiagram root001 (digits code) = true := by
  have ht := List.all_eq_true.mp class001_jobs_valid (di,ws) hm
  change (decide (ws.length = boxes001.length) &&
    (entriesHistoryFree (boxes001.zip ws) &&
      entriesValidAt directionsAt referencesAt 1378 0 di (boxes001.zip ws))) = true at ht
  have hlen := of_decide_eq_true (Bool.and_eq_true_iff.mp ht).1
  have hpair := Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp ht).2
  have hv : entriesValid 0 di (boxes001.zip ws) = true := by
    simpa only [balanced_entries_eq] using hpair.2
  exact history_free_shared_numeric_keep_implies_diagram 0 q di code retainedDiagram root001
    boxes001 ws tree001 hlen hpair.1 hq hv originalCover001 hc hkeep

#print axioms class001_jobs_valid
#print axioms class001_numeric_membership
end Snake9.Witness90
