import Balanced054Data
import BalancedGraphChecks
import LookupCover

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Shared89
open Snake9.Boxes88 Snake9.Certificate88 Snake9.Balanced89

theorem boxTable054_valid : check boxTable054 = true := by decide +kernel

theorem boxTable054_flat : flatten boxTable054 = boxes054 := by decide +kernel

theorem balancedCover054 :
    checkCoverLookup advanceBalanced 744 (fun i => lookup boxTable054 i [])
      6 [] root054 tree054 = true := by decide +kernel

theorem originalCover054 :
    checkCover retainedDiagram boxes054 6 [] root054 tree054 = true := by
  apply lookup_cover_to_original advanceBalanced 744 (fun i => lookup boxTable054 i [])
    retainedDiagram boxes054 root054 tree054
  · decide +kernel
  · intro i
    exact lookup_eq_list boxTable054 boxes054 boxTable054_valid boxTable054_flat i []
  · exact advanceBalanced_eq
  · exact balancedCover054

#print axioms boxTable054_valid
#print axioms boxTable054_flat
#print axioms balancedCover054
#print axioms originalCover054

end Snake9.Shared89
