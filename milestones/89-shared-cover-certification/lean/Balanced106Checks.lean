import Balanced106Data
import BalancedGraphChecks
import LookupCover

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Shared89
open Snake9.Boxes88 Snake9.Certificate88 Snake9.Balanced89

theorem boxTable106_valid : check boxTable106 = true := by decide +kernel

theorem boxTable106_flat : flatten boxTable106 = boxes106 := by decide +kernel

theorem balancedCover106 :
    checkCoverLookup advanceBalanced 412 (fun i => lookup boxTable106 i [])
      6 [] root106 tree106 = true := by decide +kernel

theorem originalCover106 :
    checkCover retainedDiagram boxes106 6 [] root106 tree106 = true := by
  apply lookup_cover_to_original advanceBalanced 412 (fun i => lookup boxTable106 i [])
    retainedDiagram boxes106 root106 tree106
  · decide +kernel
  · intro i
    exact lookup_eq_list boxTable106 boxes106 boxTable106_valid boxTable106_flat i []
  · exact advanceBalanced_eq
  · exact balancedCover106

#print axioms boxTable106_valid
#print axioms boxTable106_flat
#print axioms balancedCover106
#print axioms originalCover106

end Snake9.Shared89
