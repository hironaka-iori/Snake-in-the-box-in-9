import Balanced026Data
import BalancedGraphChecks
import LookupCover

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Shared89
open Snake9.Boxes88 Snake9.Certificate88 Snake9.Balanced89

theorem boxTable026_valid : check boxTable026 = true := by decide +kernel

theorem boxTable026_flat : flatten boxTable026 = boxes026 := by decide +kernel

theorem balancedCover026 :
    checkCoverLookup advanceBalanced 963 (fun i => lookup boxTable026 i [])
      6 [] root026 tree026 = true := by decide +kernel

theorem originalCover026 :
    checkCover retainedDiagram boxes026 6 [] root026 tree026 = true := by
  apply lookup_cover_to_original advanceBalanced 963 (fun i => lookup boxTable026 i [])
    retainedDiagram boxes026 root026 tree026
  · decide +kernel
  · intro i
    exact lookup_eq_list boxTable026 boxes026 boxTable026_valid boxTable026_flat i []
  · exact advanceBalanced_eq
  · exact balancedCover026

#print axioms boxTable026_valid
#print axioms boxTable026_flat
#print axioms balancedCover026
#print axioms originalCover026

end Snake9.Shared89
