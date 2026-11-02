import Balanced117Data
import BalancedGraphChecks
import LookupCover

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Shared89
open Snake9.Boxes88 Snake9.Certificate88 Snake9.Balanced89

theorem boxTable117_valid : check boxTable117 = true := by decide +kernel

theorem boxTable117_flat : flatten boxTable117 = boxes117 := by decide +kernel

theorem balancedCover117 :
    checkCoverLookup advanceBalanced 518 (fun i => lookup boxTable117 i [])
      6 [] root117 tree117 = true := by decide +kernel

theorem originalCover117 :
    checkCover retainedDiagram boxes117 6 [] root117 tree117 = true := by
  apply lookup_cover_to_original advanceBalanced 518 (fun i => lookup boxTable117 i [])
    retainedDiagram boxes117 root117 tree117
  · decide +kernel
  · intro i
    exact lookup_eq_list boxTable117 boxes117 boxTable117_valid boxTable117_flat i []
  · exact advanceBalanced_eq
  · exact balancedCover117

#print axioms boxTable117_valid
#print axioms boxTable117_flat
#print axioms balancedCover117
#print axioms originalCover117

end Snake9.Shared89
