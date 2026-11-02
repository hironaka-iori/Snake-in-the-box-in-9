import Balanced073Data
import BalancedGraphChecks
import LookupCover

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Shared89
open Snake9.Boxes88 Snake9.Certificate88 Snake9.Balanced89

theorem boxTable073_valid : check boxTable073 = true := by decide +kernel

theorem boxTable073_flat : flatten boxTable073 = boxes073 := by decide +kernel

theorem balancedCover073 :
    checkCoverLookup advanceBalanced 396 (fun i => lookup boxTable073 i [])
      6 [] root073 tree073 = true := by decide +kernel

theorem originalCover073 :
    checkCover retainedDiagram boxes073 6 [] root073 tree073 = true := by
  apply lookup_cover_to_original advanceBalanced 396 (fun i => lookup boxTable073 i [])
    retainedDiagram boxes073 root073 tree073
  · decide +kernel
  · intro i
    exact lookup_eq_list boxTable073 boxes073 boxTable073_valid boxTable073_flat i []
  · exact advanceBalanced_eq
  · exact balancedCover073

#print axioms boxTable073_valid
#print axioms boxTable073_flat
#print axioms balancedCover073
#print axioms originalCover073

end Snake9.Shared89
