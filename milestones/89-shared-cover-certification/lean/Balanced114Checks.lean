import Balanced114Data
import BalancedGraphChecks
import LookupCover

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Shared89
open Snake9.Boxes88 Snake9.Certificate88 Snake9.Balanced89

theorem boxTable114_valid : check boxTable114 = true := by decide +kernel

theorem boxTable114_flat : flatten boxTable114 = boxes114 := by decide +kernel

theorem balancedCover114 :
    checkCoverLookup advanceBalanced 672 (fun i => lookup boxTable114 i [])
      6 [] root114 tree114 = true := by decide +kernel

theorem originalCover114 :
    checkCover retainedDiagram boxes114 6 [] root114 tree114 = true := by
  apply lookup_cover_to_original advanceBalanced 672 (fun i => lookup boxTable114 i [])
    retainedDiagram boxes114 root114 tree114
  · decide +kernel
  · intro i
    exact lookup_eq_list boxTable114 boxes114 boxTable114_valid boxTable114_flat i []
  · exact advanceBalanced_eq
  · exact balancedCover114

#print axioms boxTable114_valid
#print axioms boxTable114_flat
#print axioms balancedCover114
#print axioms originalCover114

end Snake9.Shared89
