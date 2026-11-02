import Balanced005Data
import BalancedGraphChecks
import LookupCover

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Shared89
open Snake9.Boxes88 Snake9.Certificate88 Snake9.Balanced89

theorem boxTable005_valid : check boxTable005 = true := by decide +kernel

theorem boxTable005_flat : flatten boxTable005 = boxes005 := by decide +kernel

theorem balancedCover005 :
    checkCoverLookup advanceBalanced 693 (fun i => lookup boxTable005 i [])
      6 [] root005 tree005 = true := by decide +kernel

theorem originalCover005 :
    checkCover retainedDiagram boxes005 6 [] root005 tree005 = true := by
  apply lookup_cover_to_original advanceBalanced 693 (fun i => lookup boxTable005 i [])
    retainedDiagram boxes005 root005 tree005
  · decide +kernel
  · intro i
    exact lookup_eq_list boxTable005 boxes005 boxTable005_valid boxTable005_flat i []
  · exact advanceBalanced_eq
  · exact balancedCover005

#print axioms boxTable005_valid
#print axioms boxTable005_flat
#print axioms balancedCover005
#print axioms originalCover005

end Snake9.Shared89
