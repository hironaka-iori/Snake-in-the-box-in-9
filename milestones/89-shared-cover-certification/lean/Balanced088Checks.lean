import Balanced088Data
import BalancedGraphChecks
import LookupCover

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Shared89
open Snake9.Boxes88 Snake9.Certificate88 Snake9.Balanced89

theorem boxTable088_valid : check boxTable088 = true := by decide +kernel

theorem boxTable088_flat : flatten boxTable088 = boxes088 := by decide +kernel

theorem balancedCover088 :
    checkCoverLookup advanceBalanced 811 (fun i => lookup boxTable088 i [])
      6 [] root088 tree088 = true := by decide +kernel

theorem originalCover088 :
    checkCover retainedDiagram boxes088 6 [] root088 tree088 = true := by
  apply lookup_cover_to_original advanceBalanced 811 (fun i => lookup boxTable088 i [])
    retainedDiagram boxes088 root088 tree088
  · decide +kernel
  · intro i
    exact lookup_eq_list boxTable088 boxes088 boxTable088_valid boxTable088_flat i []
  · exact advanceBalanced_eq
  · exact balancedCover088

#print axioms boxTable088_valid
#print axioms boxTable088_flat
#print axioms balancedCover088
#print axioms originalCover088

end Snake9.Shared89
