import Balanced048Data
import BalancedGraphChecks
import LookupCover

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Shared89
open Snake9.Boxes88 Snake9.Certificate88 Snake9.Balanced89

theorem boxTable048_valid : check boxTable048 = true := by decide +kernel

theorem boxTable048_flat : flatten boxTable048 = boxes048 := by decide +kernel

theorem balancedCover048 :
    checkCoverLookup advanceBalanced 699 (fun i => lookup boxTable048 i [])
      6 [] root048 tree048 = true := by decide +kernel

theorem originalCover048 :
    checkCover retainedDiagram boxes048 6 [] root048 tree048 = true := by
  apply lookup_cover_to_original advanceBalanced 699 (fun i => lookup boxTable048 i [])
    retainedDiagram boxes048 root048 tree048
  · decide +kernel
  · intro i
    exact lookup_eq_list boxTable048 boxes048 boxTable048_valid boxTable048_flat i []
  · exact advanceBalanced_eq
  · exact balancedCover048

#print axioms boxTable048_valid
#print axioms boxTable048_flat
#print axioms balancedCover048
#print axioms originalCover048

end Snake9.Shared89
