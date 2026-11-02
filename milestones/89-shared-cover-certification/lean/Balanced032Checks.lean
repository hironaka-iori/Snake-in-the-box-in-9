import Balanced032Data
import BalancedGraphChecks
import LookupCover

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Shared89
open Snake9.Boxes88 Snake9.Certificate88 Snake9.Balanced89

theorem boxTable032_valid : check boxTable032 = true := by decide +kernel

theorem boxTable032_flat : flatten boxTable032 = boxes032 := by decide +kernel

theorem balancedCover032 :
    checkCoverLookup advanceBalanced 645 (fun i => lookup boxTable032 i [])
      6 [] root032 tree032 = true := by decide +kernel

theorem originalCover032 :
    checkCover retainedDiagram boxes032 6 [] root032 tree032 = true := by
  apply lookup_cover_to_original advanceBalanced 645 (fun i => lookup boxTable032 i [])
    retainedDiagram boxes032 root032 tree032
  · decide +kernel
  · intro i
    exact lookup_eq_list boxTable032 boxes032 boxTable032_valid boxTable032_flat i []
  · exact advanceBalanced_eq
  · exact balancedCover032

#print axioms boxTable032_valid
#print axioms boxTable032_flat
#print axioms balancedCover032
#print axioms originalCover032

end Snake9.Shared89
