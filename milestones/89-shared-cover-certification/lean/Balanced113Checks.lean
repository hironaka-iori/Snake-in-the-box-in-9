import Balanced113Data
import BalancedGraphChecks
import LookupCover

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Shared89
open Snake9.Boxes88 Snake9.Certificate88 Snake9.Balanced89

theorem boxTable113_valid : check boxTable113 = true := by decide +kernel

theorem boxTable113_flat : flatten boxTable113 = boxes113 := by decide +kernel

theorem balancedCover113 :
    checkCoverLookup advanceBalanced 633 (fun i => lookup boxTable113 i [])
      6 [] root113 tree113 = true := by decide +kernel

theorem originalCover113 :
    checkCover retainedDiagram boxes113 6 [] root113 tree113 = true := by
  apply lookup_cover_to_original advanceBalanced 633 (fun i => lookup boxTable113 i [])
    retainedDiagram boxes113 root113 tree113
  · decide +kernel
  · intro i
    exact lookup_eq_list boxTable113 boxes113 boxTable113_valid boxTable113_flat i []
  · exact advanceBalanced_eq
  · exact balancedCover113

#print axioms boxTable113_valid
#print axioms boxTable113_flat
#print axioms balancedCover113
#print axioms originalCover113

end Snake9.Shared89
