import Balanced033Data
import BalancedGraphChecks
import LookupCover

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Shared89
open Snake9.Boxes88 Snake9.Certificate88 Snake9.Balanced89

theorem boxTable033_valid : check boxTable033 = true := by decide +kernel

theorem boxTable033_flat : flatten boxTable033 = boxes033 := by decide +kernel

theorem balancedCover033 :
    checkCoverLookup advanceBalanced 818 (fun i => lookup boxTable033 i [])
      6 [] root033 tree033 = true := by decide +kernel

theorem originalCover033 :
    checkCover retainedDiagram boxes033 6 [] root033 tree033 = true := by
  apply lookup_cover_to_original advanceBalanced 818 (fun i => lookup boxTable033 i [])
    retainedDiagram boxes033 root033 tree033
  · decide +kernel
  · intro i
    exact lookup_eq_list boxTable033 boxes033 boxTable033_valid boxTable033_flat i []
  · exact advanceBalanced_eq
  · exact balancedCover033

#print axioms boxTable033_valid
#print axioms boxTable033_flat
#print axioms balancedCover033
#print axioms originalCover033

end Snake9.Shared89
