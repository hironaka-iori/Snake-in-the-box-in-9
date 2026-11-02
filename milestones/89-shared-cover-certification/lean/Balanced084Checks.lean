import Balanced084Data
import BalancedGraphChecks
import LookupCover

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Shared89
open Snake9.Boxes88 Snake9.Certificate88 Snake9.Balanced89

theorem boxTable084_valid : check boxTable084 = true := by decide +kernel

theorem boxTable084_flat : flatten boxTable084 = boxes084 := by decide +kernel

theorem balancedCover084 :
    checkCoverLookup advanceBalanced 683 (fun i => lookup boxTable084 i [])
      6 [] root084 tree084 = true := by decide +kernel

theorem originalCover084 :
    checkCover retainedDiagram boxes084 6 [] root084 tree084 = true := by
  apply lookup_cover_to_original advanceBalanced 683 (fun i => lookup boxTable084 i [])
    retainedDiagram boxes084 root084 tree084
  · decide +kernel
  · intro i
    exact lookup_eq_list boxTable084 boxes084 boxTable084_valid boxTable084_flat i []
  · exact advanceBalanced_eq
  · exact balancedCover084

#print axioms boxTable084_valid
#print axioms boxTable084_flat
#print axioms balancedCover084
#print axioms originalCover084

end Snake9.Shared89
