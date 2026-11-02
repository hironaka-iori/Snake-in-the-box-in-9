import Balanced047Data
import BalancedGraphChecks
import LookupCover

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Shared89
open Snake9.Boxes88 Snake9.Certificate88 Snake9.Balanced89

theorem boxTable047_valid : check boxTable047 = true := by decide +kernel

theorem boxTable047_flat : flatten boxTable047 = boxes047 := by decide +kernel

theorem balancedCover047 :
    checkCoverLookup advanceBalanced 523 (fun i => lookup boxTable047 i [])
      6 [] root047 tree047 = true := by decide +kernel

theorem originalCover047 :
    checkCover retainedDiagram boxes047 6 [] root047 tree047 = true := by
  apply lookup_cover_to_original advanceBalanced 523 (fun i => lookup boxTable047 i [])
    retainedDiagram boxes047 root047 tree047
  · decide +kernel
  · intro i
    exact lookup_eq_list boxTable047 boxes047 boxTable047_valid boxTable047_flat i []
  · exact advanceBalanced_eq
  · exact balancedCover047

#print axioms boxTable047_valid
#print axioms boxTable047_flat
#print axioms balancedCover047
#print axioms originalCover047

end Snake9.Shared89
