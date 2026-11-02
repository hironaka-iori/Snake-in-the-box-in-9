import Balanced124Data
import BalancedGraphChecks
import LookupCover

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Shared89
open Snake9.Boxes88 Snake9.Certificate88 Snake9.Balanced89

theorem boxTable124_valid : check boxTable124 = true := by decide +kernel

theorem boxTable124_flat : flatten boxTable124 = boxes124 := by decide +kernel

theorem balancedCover124 :
    checkCoverLookup advanceBalanced 604 (fun i => lookup boxTable124 i [])
      6 [] root124 tree124 = true := by decide +kernel

theorem originalCover124 :
    checkCover retainedDiagram boxes124 6 [] root124 tree124 = true := by
  apply lookup_cover_to_original advanceBalanced 604 (fun i => lookup boxTable124 i [])
    retainedDiagram boxes124 root124 tree124
  · decide +kernel
  · intro i
    exact lookup_eq_list boxTable124 boxes124 boxTable124_valid boxTable124_flat i []
  · exact advanceBalanced_eq
  · exact balancedCover124

#print axioms boxTable124_valid
#print axioms boxTable124_flat
#print axioms balancedCover124
#print axioms originalCover124

end Snake9.Shared89
