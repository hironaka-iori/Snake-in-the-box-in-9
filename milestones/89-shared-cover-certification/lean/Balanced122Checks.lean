import Balanced122Data
import BalancedGraphChecks
import LookupCover

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Shared89
open Snake9.Boxes88 Snake9.Certificate88 Snake9.Balanced89

theorem boxTable122_valid : check boxTable122 = true := by decide +kernel

theorem boxTable122_flat : flatten boxTable122 = boxes122 := by decide +kernel

theorem balancedCover122 :
    checkCoverLookup advanceBalanced 482 (fun i => lookup boxTable122 i [])
      6 [] root122 tree122 = true := by decide +kernel

theorem originalCover122 :
    checkCover retainedDiagram boxes122 6 [] root122 tree122 = true := by
  apply lookup_cover_to_original advanceBalanced 482 (fun i => lookup boxTable122 i [])
    retainedDiagram boxes122 root122 tree122
  · decide +kernel
  · intro i
    exact lookup_eq_list boxTable122 boxes122 boxTable122_valid boxTable122_flat i []
  · exact advanceBalanced_eq
  · exact balancedCover122

#print axioms boxTable122_valid
#print axioms boxTable122_flat
#print axioms balancedCover122
#print axioms originalCover122

end Snake9.Shared89
