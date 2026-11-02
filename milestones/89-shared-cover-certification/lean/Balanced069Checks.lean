import Balanced069Data
import BalancedGraphChecks
import LookupCover

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Shared89
open Snake9.Boxes88 Snake9.Certificate88 Snake9.Balanced89

theorem boxTable069_valid : check boxTable069 = true := by decide +kernel

theorem boxTable069_flat : flatten boxTable069 = boxes069 := by decide +kernel

theorem balancedCover069 :
    checkCoverLookup advanceBalanced 589 (fun i => lookup boxTable069 i [])
      6 [] root069 tree069 = true := by decide +kernel

theorem originalCover069 :
    checkCover retainedDiagram boxes069 6 [] root069 tree069 = true := by
  apply lookup_cover_to_original advanceBalanced 589 (fun i => lookup boxTable069 i [])
    retainedDiagram boxes069 root069 tree069
  · decide +kernel
  · intro i
    exact lookup_eq_list boxTable069 boxes069 boxTable069_valid boxTable069_flat i []
  · exact advanceBalanced_eq
  · exact balancedCover069

#print axioms boxTable069_valid
#print axioms boxTable069_flat
#print axioms balancedCover069
#print axioms originalCover069

end Snake9.Shared89
