import Balanced126Data
import BalancedGraphChecks
import LookupCover

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Shared89
open Snake9.Boxes88 Snake9.Certificate88 Snake9.Balanced89

theorem boxTable126_valid : check boxTable126 = true := by decide +kernel

theorem boxTable126_flat : flatten boxTable126 = boxes126 := by decide +kernel

theorem balancedCover126 :
    checkCoverLookup advanceBalanced 712 (fun i => lookup boxTable126 i [])
      6 [] root126 tree126 = true := by decide +kernel

theorem originalCover126 :
    checkCover retainedDiagram boxes126 6 [] root126 tree126 = true := by
  apply lookup_cover_to_original advanceBalanced 712 (fun i => lookup boxTable126 i [])
    retainedDiagram boxes126 root126 tree126
  · decide +kernel
  · intro i
    exact lookup_eq_list boxTable126 boxes126 boxTable126_valid boxTable126_flat i []
  · exact advanceBalanced_eq
  · exact balancedCover126

#print axioms boxTable126_valid
#print axioms boxTable126_flat
#print axioms balancedCover126
#print axioms originalCover126

end Snake9.Shared89
