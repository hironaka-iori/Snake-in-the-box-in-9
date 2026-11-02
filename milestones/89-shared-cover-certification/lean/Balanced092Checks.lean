import Balanced092Data
import BalancedGraphChecks
import LookupCover

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Shared89
open Snake9.Boxes88 Snake9.Certificate88 Snake9.Balanced89

theorem boxTable092_valid : check boxTable092 = true := by decide +kernel

theorem boxTable092_flat : flatten boxTable092 = boxes092 := by decide +kernel

theorem balancedCover092 :
    checkCoverLookup advanceBalanced 639 (fun i => lookup boxTable092 i [])
      6 [] root092 tree092 = true := by decide +kernel

theorem originalCover092 :
    checkCover retainedDiagram boxes092 6 [] root092 tree092 = true := by
  apply lookup_cover_to_original advanceBalanced 639 (fun i => lookup boxTable092 i [])
    retainedDiagram boxes092 root092 tree092
  · decide +kernel
  · intro i
    exact lookup_eq_list boxTable092 boxes092 boxTable092_valid boxTable092_flat i []
  · exact advanceBalanced_eq
  · exact balancedCover092

#print axioms boxTable092_valid
#print axioms boxTable092_flat
#print axioms balancedCover092
#print axioms originalCover092

end Snake9.Shared89
