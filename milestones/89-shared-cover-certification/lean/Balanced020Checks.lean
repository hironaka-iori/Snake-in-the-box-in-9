import Balanced020Data
import BalancedGraphChecks
import LookupCover

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Shared89
open Snake9.Boxes88 Snake9.Certificate88 Snake9.Balanced89

theorem boxTable020_valid : check boxTable020 = true := by decide +kernel

theorem boxTable020_flat : flatten boxTable020 = boxes020 := by decide +kernel

theorem balancedCover020 :
    checkCoverLookup advanceBalanced 388 (fun i => lookup boxTable020 i [])
      6 [] root020 tree020 = true := by decide +kernel

theorem originalCover020 :
    checkCover retainedDiagram boxes020 6 [] root020 tree020 = true := by
  apply lookup_cover_to_original advanceBalanced 388 (fun i => lookup boxTable020 i [])
    retainedDiagram boxes020 root020 tree020
  · decide +kernel
  · intro i
    exact lookup_eq_list boxTable020 boxes020 boxTable020_valid boxTable020_flat i []
  · exact advanceBalanced_eq
  · exact balancedCover020

#print axioms boxTable020_valid
#print axioms boxTable020_flat
#print axioms balancedCover020
#print axioms originalCover020

end Snake9.Shared89
