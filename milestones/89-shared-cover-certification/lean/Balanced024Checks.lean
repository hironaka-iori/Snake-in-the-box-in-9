import Balanced024Data
import BalancedGraphChecks
import LookupCover

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Shared89
open Snake9.Boxes88 Snake9.Certificate88 Snake9.Balanced89

theorem boxTable024_valid : check boxTable024 = true := by decide +kernel

theorem boxTable024_flat : flatten boxTable024 = boxes024 := by decide +kernel

theorem balancedCover024 :
    checkCoverLookup advanceBalanced 350 (fun i => lookup boxTable024 i [])
      6 [] root024 tree024 = true := by decide +kernel

theorem originalCover024 :
    checkCover retainedDiagram boxes024 6 [] root024 tree024 = true := by
  apply lookup_cover_to_original advanceBalanced 350 (fun i => lookup boxTable024 i [])
    retainedDiagram boxes024 root024 tree024
  · decide +kernel
  · intro i
    exact lookup_eq_list boxTable024 boxes024 boxTable024_valid boxTable024_flat i []
  · exact advanceBalanced_eq
  · exact balancedCover024

#print axioms boxTable024_valid
#print axioms boxTable024_flat
#print axioms balancedCover024
#print axioms originalCover024

end Snake9.Shared89
