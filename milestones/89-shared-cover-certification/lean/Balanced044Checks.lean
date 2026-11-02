import Balanced044Data
import BalancedGraphChecks
import LookupCover

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Shared89
open Snake9.Boxes88 Snake9.Certificate88 Snake9.Balanced89

theorem boxTable044_valid : check boxTable044 = true := by decide +kernel

theorem boxTable044_flat : flatten boxTable044 = boxes044 := by decide +kernel

theorem balancedCover044 :
    checkCoverLookup advanceBalanced 627 (fun i => lookup boxTable044 i [])
      6 [] root044 tree044 = true := by decide +kernel

theorem originalCover044 :
    checkCover retainedDiagram boxes044 6 [] root044 tree044 = true := by
  apply lookup_cover_to_original advanceBalanced 627 (fun i => lookup boxTable044 i [])
    retainedDiagram boxes044 root044 tree044
  · decide +kernel
  · intro i
    exact lookup_eq_list boxTable044 boxes044 boxTable044_valid boxTable044_flat i []
  · exact advanceBalanced_eq
  · exact balancedCover044

#print axioms boxTable044_valid
#print axioms boxTable044_flat
#print axioms balancedCover044
#print axioms originalCover044

end Snake9.Shared89
