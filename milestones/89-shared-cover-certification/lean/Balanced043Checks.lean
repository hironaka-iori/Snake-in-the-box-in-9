import Balanced043Data
import BalancedGraphChecks
import LookupCover

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Shared89
open Snake9.Boxes88 Snake9.Certificate88 Snake9.Balanced89

theorem boxTable043_valid : check boxTable043 = true := by decide +kernel

theorem boxTable043_flat : flatten boxTable043 = boxes043 := by decide +kernel

theorem balancedCover043 :
    checkCoverLookup advanceBalanced 773 (fun i => lookup boxTable043 i [])
      6 [] root043 tree043 = true := by decide +kernel

theorem originalCover043 :
    checkCover retainedDiagram boxes043 6 [] root043 tree043 = true := by
  apply lookup_cover_to_original advanceBalanced 773 (fun i => lookup boxTable043 i [])
    retainedDiagram boxes043 root043 tree043
  · decide +kernel
  · intro i
    exact lookup_eq_list boxTable043 boxes043 boxTable043_valid boxTable043_flat i []
  · exact advanceBalanced_eq
  · exact balancedCover043

#print axioms boxTable043_valid
#print axioms boxTable043_flat
#print axioms balancedCover043
#print axioms originalCover043

end Snake9.Shared89
