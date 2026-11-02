import Balanced079Data
import BalancedGraphChecks
import LookupCover

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Shared89
open Snake9.Boxes88 Snake9.Certificate88 Snake9.Balanced89

theorem boxTable079_valid : check boxTable079 = true := by decide +kernel

theorem boxTable079_flat : flatten boxTable079 = boxes079 := by decide +kernel

theorem balancedCover079 :
    checkCoverLookup advanceBalanced 381 (fun i => lookup boxTable079 i [])
      6 [] root079 tree079 = true := by decide +kernel

theorem originalCover079 :
    checkCover retainedDiagram boxes079 6 [] root079 tree079 = true := by
  apply lookup_cover_to_original advanceBalanced 381 (fun i => lookup boxTable079 i [])
    retainedDiagram boxes079 root079 tree079
  · decide +kernel
  · intro i
    exact lookup_eq_list boxTable079 boxes079 boxTable079_valid boxTable079_flat i []
  · exact advanceBalanced_eq
  · exact balancedCover079

#print axioms boxTable079_valid
#print axioms boxTable079_flat
#print axioms balancedCover079
#print axioms originalCover079

end Snake9.Shared89
