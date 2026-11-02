import Balanced094Data
import BalancedGraphChecks
import LookupCover

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Shared89
open Snake9.Boxes88 Snake9.Certificate88 Snake9.Balanced89

theorem boxTable094_valid : check boxTable094 = true := by decide +kernel

theorem boxTable094_flat : flatten boxTable094 = boxes094 := by decide +kernel

theorem balancedCover094 :
    checkCoverLookup advanceBalanced 769 (fun i => lookup boxTable094 i [])
      6 [] root094 tree094 = true := by decide +kernel

theorem originalCover094 :
    checkCover retainedDiagram boxes094 6 [] root094 tree094 = true := by
  apply lookup_cover_to_original advanceBalanced 769 (fun i => lookup boxTable094 i [])
    retainedDiagram boxes094 root094 tree094
  · decide +kernel
  · intro i
    exact lookup_eq_list boxTable094 boxes094 boxTable094_valid boxTable094_flat i []
  · exact advanceBalanced_eq
  · exact balancedCover094

#print axioms boxTable094_valid
#print axioms boxTable094_flat
#print axioms balancedCover094
#print axioms originalCover094

end Snake9.Shared89
