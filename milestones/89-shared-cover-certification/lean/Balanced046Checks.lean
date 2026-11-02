import Balanced046Data
import BalancedGraphChecks
import LookupCover

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Shared89
open Snake9.Boxes88 Snake9.Certificate88 Snake9.Balanced89

theorem boxTable046_valid : check boxTable046 = true := by decide +kernel

theorem boxTable046_flat : flatten boxTable046 = boxes046 := by decide +kernel

theorem balancedCover046 :
    checkCoverLookup advanceBalanced 681 (fun i => lookup boxTable046 i [])
      6 [] root046 tree046 = true := by decide +kernel

theorem originalCover046 :
    checkCover retainedDiagram boxes046 6 [] root046 tree046 = true := by
  apply lookup_cover_to_original advanceBalanced 681 (fun i => lookup boxTable046 i [])
    retainedDiagram boxes046 root046 tree046
  · decide +kernel
  · intro i
    exact lookup_eq_list boxTable046 boxes046 boxTable046_valid boxTable046_flat i []
  · exact advanceBalanced_eq
  · exact balancedCover046

#print axioms boxTable046_valid
#print axioms boxTable046_flat
#print axioms balancedCover046
#print axioms originalCover046

end Snake9.Shared89
