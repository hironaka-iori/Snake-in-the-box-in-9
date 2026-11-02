import Balanced021Data
import BalancedGraphChecks
import LookupCover

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Shared89
open Snake9.Boxes88 Snake9.Certificate88 Snake9.Balanced89

theorem boxTable021_valid : check boxTable021 = true := by decide +kernel

theorem boxTable021_flat : flatten boxTable021 = boxes021 := by decide +kernel

theorem balancedCover021 :
    checkCoverLookup advanceBalanced 674 (fun i => lookup boxTable021 i [])
      6 [] root021 tree021 = true := by decide +kernel

theorem originalCover021 :
    checkCover retainedDiagram boxes021 6 [] root021 tree021 = true := by
  apply lookup_cover_to_original advanceBalanced 674 (fun i => lookup boxTable021 i [])
    retainedDiagram boxes021 root021 tree021
  · decide +kernel
  · intro i
    exact lookup_eq_list boxTable021 boxes021 boxTable021_valid boxTable021_flat i []
  · exact advanceBalanced_eq
  · exact balancedCover021

#print axioms boxTable021_valid
#print axioms boxTable021_flat
#print axioms balancedCover021
#print axioms originalCover021

end Snake9.Shared89
