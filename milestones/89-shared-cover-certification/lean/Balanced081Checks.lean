import Balanced081Data
import BalancedGraphChecks
import LookupCover

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Shared89
open Snake9.Boxes88 Snake9.Certificate88 Snake9.Balanced89

theorem boxTable081_valid : check boxTable081 = true := by decide +kernel

theorem boxTable081_flat : flatten boxTable081 = boxes081 := by decide +kernel

theorem balancedCover081 :
    checkCoverLookup advanceBalanced 749 (fun i => lookup boxTable081 i [])
      6 [] root081 tree081 = true := by decide +kernel

theorem originalCover081 :
    checkCover retainedDiagram boxes081 6 [] root081 tree081 = true := by
  apply lookup_cover_to_original advanceBalanced 749 (fun i => lookup boxTable081 i [])
    retainedDiagram boxes081 root081 tree081
  · decide +kernel
  · intro i
    exact lookup_eq_list boxTable081 boxes081 boxTable081_valid boxTable081_flat i []
  · exact advanceBalanced_eq
  · exact balancedCover081

#print axioms boxTable081_valid
#print axioms boxTable081_flat
#print axioms balancedCover081
#print axioms originalCover081

end Snake9.Shared89
