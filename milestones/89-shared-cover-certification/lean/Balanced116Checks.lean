import Balanced116Data
import BalancedGraphChecks
import LookupCover

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Shared89
open Snake9.Boxes88 Snake9.Certificate88 Snake9.Balanced89

theorem boxTable116_valid : check boxTable116 = true := by decide +kernel

theorem boxTable116_flat : flatten boxTable116 = boxes116 := by decide +kernel

theorem balancedCover116 :
    checkCoverLookup advanceBalanced 674 (fun i => lookup boxTable116 i [])
      6 [] root116 tree116 = true := by decide +kernel

theorem originalCover116 :
    checkCover retainedDiagram boxes116 6 [] root116 tree116 = true := by
  apply lookup_cover_to_original advanceBalanced 674 (fun i => lookup boxTable116 i [])
    retainedDiagram boxes116 root116 tree116
  · decide +kernel
  · intro i
    exact lookup_eq_list boxTable116 boxes116 boxTable116_valid boxTable116_flat i []
  · exact advanceBalanced_eq
  · exact balancedCover116

#print axioms boxTable116_valid
#print axioms boxTable116_flat
#print axioms balancedCover116
#print axioms originalCover116

end Snake9.Shared89
