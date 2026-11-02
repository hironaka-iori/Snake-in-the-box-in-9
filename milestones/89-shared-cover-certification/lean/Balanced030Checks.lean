import Balanced030Data
import BalancedGraphChecks
import LookupCover

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Shared89
open Snake9.Boxes88 Snake9.Certificate88 Snake9.Balanced89

theorem boxTable030_valid : check boxTable030 = true := by decide +kernel

theorem boxTable030_flat : flatten boxTable030 = boxes030 := by decide +kernel

theorem balancedCover030 :
    checkCoverLookup advanceBalanced 818 (fun i => lookup boxTable030 i [])
      6 [] root030 tree030 = true := by decide +kernel

theorem originalCover030 :
    checkCover retainedDiagram boxes030 6 [] root030 tree030 = true := by
  apply lookup_cover_to_original advanceBalanced 818 (fun i => lookup boxTable030 i [])
    retainedDiagram boxes030 root030 tree030
  · decide +kernel
  · intro i
    exact lookup_eq_list boxTable030 boxes030 boxTable030_valid boxTable030_flat i []
  · exact advanceBalanced_eq
  · exact balancedCover030

#print axioms boxTable030_valid
#print axioms boxTable030_flat
#print axioms balancedCover030
#print axioms originalCover030

end Snake9.Shared89
