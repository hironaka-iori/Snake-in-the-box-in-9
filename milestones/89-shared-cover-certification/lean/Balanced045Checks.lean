import Balanced045Data
import BalancedGraphChecks
import LookupCover

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Shared89
open Snake9.Boxes88 Snake9.Certificate88 Snake9.Balanced89

theorem boxTable045_valid : check boxTable045 = true := by decide +kernel

theorem boxTable045_flat : flatten boxTable045 = boxes045 := by decide +kernel

theorem balancedCover045 :
    checkCoverLookup advanceBalanced 394 (fun i => lookup boxTable045 i [])
      6 [] root045 tree045 = true := by decide +kernel

theorem originalCover045 :
    checkCover retainedDiagram boxes045 6 [] root045 tree045 = true := by
  apply lookup_cover_to_original advanceBalanced 394 (fun i => lookup boxTable045 i [])
    retainedDiagram boxes045 root045 tree045
  · decide +kernel
  · intro i
    exact lookup_eq_list boxTable045 boxes045 boxTable045_valid boxTable045_flat i []
  · exact advanceBalanced_eq
  · exact balancedCover045

#print axioms boxTable045_valid
#print axioms boxTable045_flat
#print axioms balancedCover045
#print axioms originalCover045

end Snake9.Shared89
