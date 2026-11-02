import Balanced065Data
import BalancedGraphChecks
import LookupCover

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Shared89
open Snake9.Boxes88 Snake9.Certificate88 Snake9.Balanced89

theorem boxTable065_valid : check boxTable065 = true := by decide +kernel

theorem boxTable065_flat : flatten boxTable065 = boxes065 := by decide +kernel

theorem balancedCover065 :
    checkCoverLookup advanceBalanced 689 (fun i => lookup boxTable065 i [])
      6 [] root065 tree065 = true := by decide +kernel

theorem originalCover065 :
    checkCover retainedDiagram boxes065 6 [] root065 tree065 = true := by
  apply lookup_cover_to_original advanceBalanced 689 (fun i => lookup boxTable065 i [])
    retainedDiagram boxes065 root065 tree065
  · decide +kernel
  · intro i
    exact lookup_eq_list boxTable065 boxes065 boxTable065_valid boxTable065_flat i []
  · exact advanceBalanced_eq
  · exact balancedCover065

#print axioms boxTable065_valid
#print axioms boxTable065_flat
#print axioms balancedCover065
#print axioms originalCover065

end Snake9.Shared89
