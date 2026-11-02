import Balanced052Data
import BalancedGraphChecks
import LookupCover

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Shared89
open Snake9.Boxes88 Snake9.Certificate88 Snake9.Balanced89

theorem boxTable052_valid : check boxTable052 = true := by decide +kernel

theorem boxTable052_flat : flatten boxTable052 = boxes052 := by decide +kernel

theorem balancedCover052 :
    checkCoverLookup advanceBalanced 582 (fun i => lookup boxTable052 i [])
      6 [] root052 tree052 = true := by decide +kernel

theorem originalCover052 :
    checkCover retainedDiagram boxes052 6 [] root052 tree052 = true := by
  apply lookup_cover_to_original advanceBalanced 582 (fun i => lookup boxTable052 i [])
    retainedDiagram boxes052 root052 tree052
  · decide +kernel
  · intro i
    exact lookup_eq_list boxTable052 boxes052 boxTable052_valid boxTable052_flat i []
  · exact advanceBalanced_eq
  · exact balancedCover052

#print axioms boxTable052_valid
#print axioms boxTable052_flat
#print axioms balancedCover052
#print axioms originalCover052

end Snake9.Shared89
