import Balanced057Data
import BalancedGraphChecks
import LookupCover

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Shared89
open Snake9.Boxes88 Snake9.Certificate88 Snake9.Balanced89

theorem boxTable057_valid : check boxTable057 = true := by decide +kernel

theorem boxTable057_flat : flatten boxTable057 = boxes057 := by decide +kernel

theorem balancedCover057 :
    checkCoverLookup advanceBalanced 950 (fun i => lookup boxTable057 i [])
      6 [] root057 tree057 = true := by decide +kernel

theorem originalCover057 :
    checkCover retainedDiagram boxes057 6 [] root057 tree057 = true := by
  apply lookup_cover_to_original advanceBalanced 950 (fun i => lookup boxTable057 i [])
    retainedDiagram boxes057 root057 tree057
  · decide +kernel
  · intro i
    exact lookup_eq_list boxTable057 boxes057 boxTable057_valid boxTable057_flat i []
  · exact advanceBalanced_eq
  · exact balancedCover057

#print axioms boxTable057_valid
#print axioms boxTable057_flat
#print axioms balancedCover057
#print axioms originalCover057

end Snake9.Shared89
