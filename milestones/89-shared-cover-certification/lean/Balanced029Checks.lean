import Balanced029Data
import BalancedGraphChecks
import LookupCover

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Shared89
open Snake9.Boxes88 Snake9.Certificate88 Snake9.Balanced89

theorem boxTable029_valid : check boxTable029 = true := by decide +kernel

theorem boxTable029_flat : flatten boxTable029 = boxes029 := by decide +kernel

theorem balancedCover029 :
    checkCoverLookup advanceBalanced 764 (fun i => lookup boxTable029 i [])
      6 [] root029 tree029 = true := by decide +kernel

theorem originalCover029 :
    checkCover retainedDiagram boxes029 6 [] root029 tree029 = true := by
  apply lookup_cover_to_original advanceBalanced 764 (fun i => lookup boxTable029 i [])
    retainedDiagram boxes029 root029 tree029
  · decide +kernel
  · intro i
    exact lookup_eq_list boxTable029 boxes029 boxTable029_valid boxTable029_flat i []
  · exact advanceBalanced_eq
  · exact balancedCover029

#print axioms boxTable029_valid
#print axioms boxTable029_flat
#print axioms balancedCover029
#print axioms originalCover029

end Snake9.Shared89
