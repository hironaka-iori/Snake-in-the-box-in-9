import Balanced098Data
import BalancedGraphChecks
import LookupCover

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Shared89
open Snake9.Boxes88 Snake9.Certificate88 Snake9.Balanced89

theorem boxTable098_valid : check boxTable098 = true := by decide +kernel

theorem boxTable098_flat : flatten boxTable098 = boxes098 := by decide +kernel

theorem balancedCover098 :
    checkCoverLookup advanceBalanced 837 (fun i => lookup boxTable098 i [])
      6 [] root098 tree098 = true := by decide +kernel

theorem originalCover098 :
    checkCover retainedDiagram boxes098 6 [] root098 tree098 = true := by
  apply lookup_cover_to_original advanceBalanced 837 (fun i => lookup boxTable098 i [])
    retainedDiagram boxes098 root098 tree098
  · decide +kernel
  · intro i
    exact lookup_eq_list boxTable098 boxes098 boxTable098_valid boxTable098_flat i []
  · exact advanceBalanced_eq
  · exact balancedCover098

#print axioms boxTable098_valid
#print axioms boxTable098_flat
#print axioms balancedCover098
#print axioms originalCover098

end Snake9.Shared89
