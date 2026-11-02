import Balanced121Data
import BalancedGraphChecks
import LookupCover

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Shared89
open Snake9.Boxes88 Snake9.Certificate88 Snake9.Balanced89

theorem boxTable121_valid : check boxTable121 = true := by decide +kernel

theorem boxTable121_flat : flatten boxTable121 = boxes121 := by decide +kernel

theorem balancedCover121 :
    checkCoverLookup advanceBalanced 481 (fun i => lookup boxTable121 i [])
      6 [] root121 tree121 = true := by decide +kernel

theorem originalCover121 :
    checkCover retainedDiagram boxes121 6 [] root121 tree121 = true := by
  apply lookup_cover_to_original advanceBalanced 481 (fun i => lookup boxTable121 i [])
    retainedDiagram boxes121 root121 tree121
  · decide +kernel
  · intro i
    exact lookup_eq_list boxTable121 boxes121 boxTable121_valid boxTable121_flat i []
  · exact advanceBalanced_eq
  · exact balancedCover121

#print axioms boxTable121_valid
#print axioms boxTable121_flat
#print axioms balancedCover121
#print axioms originalCover121

end Snake9.Shared89
