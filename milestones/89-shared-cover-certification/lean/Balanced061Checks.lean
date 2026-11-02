import Balanced061Data
import BalancedGraphChecks
import LookupCover

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Shared89
open Snake9.Boxes88 Snake9.Certificate88 Snake9.Balanced89

theorem boxTable061_valid : check boxTable061 = true := by decide +kernel

theorem boxTable061_flat : flatten boxTable061 = boxes061 := by decide +kernel

theorem balancedCover061 :
    checkCoverLookup advanceBalanced 649 (fun i => lookup boxTable061 i [])
      6 [] root061 tree061 = true := by decide +kernel

theorem originalCover061 :
    checkCover retainedDiagram boxes061 6 [] root061 tree061 = true := by
  apply lookup_cover_to_original advanceBalanced 649 (fun i => lookup boxTable061 i [])
    retainedDiagram boxes061 root061 tree061
  · decide +kernel
  · intro i
    exact lookup_eq_list boxTable061 boxes061 boxTable061_valid boxTable061_flat i []
  · exact advanceBalanced_eq
  · exact balancedCover061

#print axioms boxTable061_valid
#print axioms boxTable061_flat
#print axioms balancedCover061
#print axioms originalCover061

end Snake9.Shared89
