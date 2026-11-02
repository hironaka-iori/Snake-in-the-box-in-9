import Balanced072Data
import BalancedGraphChecks
import LookupCover

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Shared89
open Snake9.Boxes88 Snake9.Certificate88 Snake9.Balanced89

theorem boxTable072_valid : check boxTable072 = true := by decide +kernel

theorem boxTable072_flat : flatten boxTable072 = boxes072 := by decide +kernel

theorem balancedCover072 :
    checkCoverLookup advanceBalanced 616 (fun i => lookup boxTable072 i [])
      6 [] root072 tree072 = true := by decide +kernel

theorem originalCover072 :
    checkCover retainedDiagram boxes072 6 [] root072 tree072 = true := by
  apply lookup_cover_to_original advanceBalanced 616 (fun i => lookup boxTable072 i [])
    retainedDiagram boxes072 root072 tree072
  · decide +kernel
  · intro i
    exact lookup_eq_list boxTable072 boxes072 boxTable072_valid boxTable072_flat i []
  · exact advanceBalanced_eq
  · exact balancedCover072

#print axioms boxTable072_valid
#print axioms boxTable072_flat
#print axioms balancedCover072
#print axioms originalCover072

end Snake9.Shared89
