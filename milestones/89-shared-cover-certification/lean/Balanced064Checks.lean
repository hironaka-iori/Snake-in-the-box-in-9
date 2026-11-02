import Balanced064Data
import BalancedGraphChecks
import LookupCover

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Shared89
open Snake9.Boxes88 Snake9.Certificate88 Snake9.Balanced89

theorem boxTable064_valid : check boxTable064 = true := by decide +kernel

theorem boxTable064_flat : flatten boxTable064 = boxes064 := by decide +kernel

theorem balancedCover064 :
    checkCoverLookup advanceBalanced 808 (fun i => lookup boxTable064 i [])
      6 [] root064 tree064 = true := by decide +kernel

theorem originalCover064 :
    checkCover retainedDiagram boxes064 6 [] root064 tree064 = true := by
  apply lookup_cover_to_original advanceBalanced 808 (fun i => lookup boxTable064 i [])
    retainedDiagram boxes064 root064 tree064
  · decide +kernel
  · intro i
    exact lookup_eq_list boxTable064 boxes064 boxTable064_valid boxTable064_flat i []
  · exact advanceBalanced_eq
  · exact balancedCover064

#print axioms boxTable064_valid
#print axioms boxTable064_flat
#print axioms balancedCover064
#print axioms originalCover064

end Snake9.Shared89
