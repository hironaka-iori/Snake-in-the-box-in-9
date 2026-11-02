import Balanced119Data
import BalancedGraphChecks
import LookupCover

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Shared89
open Snake9.Boxes88 Snake9.Certificate88 Snake9.Balanced89

theorem boxTable119_valid : check boxTable119 = true := by decide +kernel

theorem boxTable119_flat : flatten boxTable119 = boxes119 := by decide +kernel

theorem balancedCover119 :
    checkCoverLookup advanceBalanced 600 (fun i => lookup boxTable119 i [])
      6 [] root119 tree119 = true := by decide +kernel

theorem originalCover119 :
    checkCover retainedDiagram boxes119 6 [] root119 tree119 = true := by
  apply lookup_cover_to_original advanceBalanced 600 (fun i => lookup boxTable119 i [])
    retainedDiagram boxes119 root119 tree119
  · decide +kernel
  · intro i
    exact lookup_eq_list boxTable119 boxes119 boxTable119_valid boxTable119_flat i []
  · exact advanceBalanced_eq
  · exact balancedCover119

#print axioms boxTable119_valid
#print axioms boxTable119_flat
#print axioms balancedCover119
#print axioms originalCover119

end Snake9.Shared89
