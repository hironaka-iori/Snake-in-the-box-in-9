import Balanced070Data
import BalancedGraphChecks
import LookupCover

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Shared89
open Snake9.Boxes88 Snake9.Certificate88 Snake9.Balanced89

theorem boxTable070_valid : check boxTable070 = true := by decide +kernel

theorem boxTable070_flat : flatten boxTable070 = boxes070 := by decide +kernel

theorem balancedCover070 :
    checkCoverLookup advanceBalanced 408 (fun i => lookup boxTable070 i [])
      6 [] root070 tree070 = true := by decide +kernel

theorem originalCover070 :
    checkCover retainedDiagram boxes070 6 [] root070 tree070 = true := by
  apply lookup_cover_to_original advanceBalanced 408 (fun i => lookup boxTable070 i [])
    retainedDiagram boxes070 root070 tree070
  · decide +kernel
  · intro i
    exact lookup_eq_list boxTable070 boxes070 boxTable070_valid boxTable070_flat i []
  · exact advanceBalanced_eq
  · exact balancedCover070

#print axioms boxTable070_valid
#print axioms boxTable070_flat
#print axioms balancedCover070
#print axioms originalCover070

end Snake9.Shared89
