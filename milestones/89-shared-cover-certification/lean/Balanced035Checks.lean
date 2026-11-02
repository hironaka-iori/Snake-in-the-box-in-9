import Balanced035Data
import BalancedGraphChecks
import LookupCover

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Shared89
open Snake9.Boxes88 Snake9.Certificate88 Snake9.Balanced89

theorem boxTable035_valid : check boxTable035 = true := by decide +kernel

theorem boxTable035_flat : flatten boxTable035 = boxes035 := by decide +kernel

theorem balancedCover035 :
    checkCoverLookup advanceBalanced 683 (fun i => lookup boxTable035 i [])
      6 [] root035 tree035 = true := by decide +kernel

theorem originalCover035 :
    checkCover retainedDiagram boxes035 6 [] root035 tree035 = true := by
  apply lookup_cover_to_original advanceBalanced 683 (fun i => lookup boxTable035 i [])
    retainedDiagram boxes035 root035 tree035
  · decide +kernel
  · intro i
    exact lookup_eq_list boxTable035 boxes035 boxTable035_valid boxTable035_flat i []
  · exact advanceBalanced_eq
  · exact balancedCover035

#print axioms boxTable035_valid
#print axioms boxTable035_flat
#print axioms balancedCover035
#print axioms originalCover035

end Snake9.Shared89
