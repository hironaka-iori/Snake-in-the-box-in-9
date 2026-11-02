import Balanced089Data
import BalancedGraphChecks
import LookupCover

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Shared89
open Snake9.Boxes88 Snake9.Certificate88 Snake9.Balanced89

theorem boxTable089_valid : check boxTable089 = true := by decide +kernel

theorem boxTable089_flat : flatten boxTable089 = boxes089 := by decide +kernel

theorem balancedCover089 :
    checkCoverLookup advanceBalanced 616 (fun i => lookup boxTable089 i [])
      6 [] root089 tree089 = true := by decide +kernel

theorem originalCover089 :
    checkCover retainedDiagram boxes089 6 [] root089 tree089 = true := by
  apply lookup_cover_to_original advanceBalanced 616 (fun i => lookup boxTable089 i [])
    retainedDiagram boxes089 root089 tree089
  · decide +kernel
  · intro i
    exact lookup_eq_list boxTable089 boxes089 boxTable089_valid boxTable089_flat i []
  · exact advanceBalanced_eq
  · exact balancedCover089

#print axioms boxTable089_valid
#print axioms boxTable089_flat
#print axioms balancedCover089
#print axioms originalCover089

end Snake9.Shared89
