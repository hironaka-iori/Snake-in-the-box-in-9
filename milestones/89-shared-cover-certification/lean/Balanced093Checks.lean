import Balanced093Data
import BalancedGraphChecks
import LookupCover

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Shared89
open Snake9.Boxes88 Snake9.Certificate88 Snake9.Balanced89

theorem boxTable093_valid : check boxTable093 = true := by decide +kernel

theorem boxTable093_flat : flatten boxTable093 = boxes093 := by decide +kernel

theorem balancedCover093 :
    checkCoverLookup advanceBalanced 404 (fun i => lookup boxTable093 i [])
      6 [] root093 tree093 = true := by decide +kernel

theorem originalCover093 :
    checkCover retainedDiagram boxes093 6 [] root093 tree093 = true := by
  apply lookup_cover_to_original advanceBalanced 404 (fun i => lookup boxTable093 i [])
    retainedDiagram boxes093 root093 tree093
  · decide +kernel
  · intro i
    exact lookup_eq_list boxTable093 boxes093 boxTable093_valid boxTable093_flat i []
  · exact advanceBalanced_eq
  · exact balancedCover093

#print axioms boxTable093_valid
#print axioms boxTable093_flat
#print axioms balancedCover093
#print axioms originalCover093

end Snake9.Shared89
