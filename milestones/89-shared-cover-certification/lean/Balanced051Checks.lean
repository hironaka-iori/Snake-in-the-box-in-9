import Balanced051Data
import BalancedGraphChecks
import LookupCover

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Shared89
open Snake9.Boxes88 Snake9.Certificate88 Snake9.Balanced89

theorem boxTable051_valid : check boxTable051 = true := by decide +kernel

theorem boxTable051_flat : flatten boxTable051 = boxes051 := by decide +kernel

theorem balancedCover051 :
    checkCoverLookup advanceBalanced 643 (fun i => lookup boxTable051 i [])
      6 [] root051 tree051 = true := by decide +kernel

theorem originalCover051 :
    checkCover retainedDiagram boxes051 6 [] root051 tree051 = true := by
  apply lookup_cover_to_original advanceBalanced 643 (fun i => lookup boxTable051 i [])
    retainedDiagram boxes051 root051 tree051
  · decide +kernel
  · intro i
    exact lookup_eq_list boxTable051 boxes051 boxTable051_valid boxTable051_flat i []
  · exact advanceBalanced_eq
  · exact balancedCover051

#print axioms boxTable051_valid
#print axioms boxTable051_flat
#print axioms balancedCover051
#print axioms originalCover051

end Snake9.Shared89
