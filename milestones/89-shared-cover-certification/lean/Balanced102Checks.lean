import Balanced102Data
import BalancedGraphChecks
import LookupCover

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Shared89
open Snake9.Boxes88 Snake9.Certificate88 Snake9.Balanced89

theorem boxTable102_valid : check boxTable102 = true := by decide +kernel

theorem boxTable102_flat : flatten boxTable102 = boxes102 := by decide +kernel

theorem balancedCover102 :
    checkCoverLookup advanceBalanced 858 (fun i => lookup boxTable102 i [])
      6 [] root102 tree102 = true := by decide +kernel

theorem originalCover102 :
    checkCover retainedDiagram boxes102 6 [] root102 tree102 = true := by
  apply lookup_cover_to_original advanceBalanced 858 (fun i => lookup boxTable102 i [])
    retainedDiagram boxes102 root102 tree102
  · decide +kernel
  · intro i
    exact lookup_eq_list boxTable102 boxes102 boxTable102_valid boxTable102_flat i []
  · exact advanceBalanced_eq
  · exact balancedCover102

#print axioms boxTable102_valid
#print axioms boxTable102_flat
#print axioms balancedCover102
#print axioms originalCover102

end Snake9.Shared89
