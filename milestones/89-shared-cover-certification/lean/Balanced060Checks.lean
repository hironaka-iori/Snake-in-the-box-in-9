import Balanced060Data
import BalancedGraphChecks
import LookupCover

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Shared89
open Snake9.Boxes88 Snake9.Certificate88 Snake9.Balanced89

theorem boxTable060_valid : check boxTable060 = true := by decide +kernel

theorem boxTable060_flat : flatten boxTable060 = boxes060 := by decide +kernel

theorem balancedCover060 :
    checkCoverLookup advanceBalanced 783 (fun i => lookup boxTable060 i [])
      6 [] root060 tree060 = true := by decide +kernel

theorem originalCover060 :
    checkCover retainedDiagram boxes060 6 [] root060 tree060 = true := by
  apply lookup_cover_to_original advanceBalanced 783 (fun i => lookup boxTable060 i [])
    retainedDiagram boxes060 root060 tree060
  · decide +kernel
  · intro i
    exact lookup_eq_list boxTable060 boxes060 boxTable060_valid boxTable060_flat i []
  · exact advanceBalanced_eq
  · exact balancedCover060

#print axioms boxTable060_valid
#print axioms boxTable060_flat
#print axioms balancedCover060
#print axioms originalCover060

end Snake9.Shared89
