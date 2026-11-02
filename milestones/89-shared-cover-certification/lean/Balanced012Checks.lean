import Balanced012Data
import BalancedGraphChecks
import LookupCover

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Shared89
open Snake9.Boxes88 Snake9.Certificate88 Snake9.Balanced89

theorem boxTable012_valid : check boxTable012 = true := by decide +kernel

theorem boxTable012_flat : flatten boxTable012 = boxes012 := by decide +kernel

theorem balancedCover012 :
    checkCoverLookup advanceBalanced 651 (fun i => lookup boxTable012 i [])
      6 [] root012 tree012 = true := by decide +kernel

theorem originalCover012 :
    checkCover retainedDiagram boxes012 6 [] root012 tree012 = true := by
  apply lookup_cover_to_original advanceBalanced 651 (fun i => lookup boxTable012 i [])
    retainedDiagram boxes012 root012 tree012
  · decide +kernel
  · intro i
    exact lookup_eq_list boxTable012 boxes012 boxTable012_valid boxTable012_flat i []
  · exact advanceBalanced_eq
  · exact balancedCover012

#print axioms boxTable012_valid
#print axioms boxTable012_flat
#print axioms balancedCover012
#print axioms originalCover012

end Snake9.Shared89
