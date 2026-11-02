import Balanced104Data
import BalancedGraphChecks
import LookupCover

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Shared89
open Snake9.Boxes88 Snake9.Certificate88 Snake9.Balanced89

theorem boxTable104_valid : check boxTable104 = true := by decide +kernel

theorem boxTable104_flat : flatten boxTable104 = boxes104 := by decide +kernel

theorem balancedCover104 :
    checkCoverLookup advanceBalanced 546 (fun i => lookup boxTable104 i [])
      6 [] root104 tree104 = true := by decide +kernel

theorem originalCover104 :
    checkCover retainedDiagram boxes104 6 [] root104 tree104 = true := by
  apply lookup_cover_to_original advanceBalanced 546 (fun i => lookup boxTable104 i [])
    retainedDiagram boxes104 root104 tree104
  · decide +kernel
  · intro i
    exact lookup_eq_list boxTable104 boxes104 boxTable104_valid boxTable104_flat i []
  · exact advanceBalanced_eq
  · exact balancedCover104

#print axioms boxTable104_valid
#print axioms boxTable104_flat
#print axioms balancedCover104
#print axioms originalCover104

end Snake9.Shared89
