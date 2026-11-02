import Balanced109Data
import BalancedGraphChecks
import LookupCover

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Shared89
open Snake9.Boxes88 Snake9.Certificate88 Snake9.Balanced89

theorem boxTable109_valid : check boxTable109 = true := by decide +kernel

theorem boxTable109_flat : flatten boxTable109 = boxes109 := by decide +kernel

theorem balancedCover109 :
    checkCoverLookup advanceBalanced 762 (fun i => lookup boxTable109 i [])
      6 [] root109 tree109 = true := by decide +kernel

theorem originalCover109 :
    checkCover retainedDiagram boxes109 6 [] root109 tree109 = true := by
  apply lookup_cover_to_original advanceBalanced 762 (fun i => lookup boxTable109 i [])
    retainedDiagram boxes109 root109 tree109
  · decide +kernel
  · intro i
    exact lookup_eq_list boxTable109 boxes109 boxTable109_valid boxTable109_flat i []
  · exact advanceBalanced_eq
  · exact balancedCover109

#print axioms boxTable109_valid
#print axioms boxTable109_flat
#print axioms balancedCover109
#print axioms originalCover109

end Snake9.Shared89
