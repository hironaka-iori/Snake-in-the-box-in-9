import Balanced000Data
import BalancedGraphChecks
import LookupCover

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Shared89
open Snake9.Boxes88 Snake9.Certificate88 Snake9.Balanced89

theorem boxTable000_valid : check boxTable000 = true := by decide +kernel

theorem boxTable000_flat : flatten boxTable000 = boxes000 := by decide +kernel

theorem balancedCover000 :
    checkCoverLookup advanceBalanced 375 (fun i => lookup boxTable000 i [])
      6 [] root000 tree000 = true := by decide +kernel

theorem originalCover000 :
    checkCover retainedDiagram boxes000 6 [] root000 tree000 = true := by
  apply lookup_cover_to_original advanceBalanced 375 (fun i => lookup boxTable000 i [])
    retainedDiagram boxes000 root000 tree000
  · decide +kernel
  · intro i
    exact lookup_eq_list boxTable000 boxes000 boxTable000_valid boxTable000_flat i []
  · exact advanceBalanced_eq
  · exact balancedCover000

#print axioms boxTable000_valid
#print axioms boxTable000_flat
#print axioms balancedCover000
#print axioms originalCover000

end Snake9.Shared89
