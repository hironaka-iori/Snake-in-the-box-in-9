import Balanced062Data
import BalancedGraphChecks
import LookupCover

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Shared89
open Snake9.Boxes88 Snake9.Certificate88 Snake9.Balanced89

theorem boxTable062_valid : check boxTable062 = true := by decide +kernel

theorem boxTable062_flat : flatten boxTable062 = boxes062 := by decide +kernel

theorem balancedCover062 :
    checkCoverLookup advanceBalanced 497 (fun i => lookup boxTable062 i [])
      6 [] root062 tree062 = true := by decide +kernel

theorem originalCover062 :
    checkCover retainedDiagram boxes062 6 [] root062 tree062 = true := by
  apply lookup_cover_to_original advanceBalanced 497 (fun i => lookup boxTable062 i [])
    retainedDiagram boxes062 root062 tree062
  · decide +kernel
  · intro i
    exact lookup_eq_list boxTable062 boxes062 boxTable062_valid boxTable062_flat i []
  · exact advanceBalanced_eq
  · exact balancedCover062

#print axioms boxTable062_valid
#print axioms boxTable062_flat
#print axioms balancedCover062
#print axioms originalCover062

end Snake9.Shared89
