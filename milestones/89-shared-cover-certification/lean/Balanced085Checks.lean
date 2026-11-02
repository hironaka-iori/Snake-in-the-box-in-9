import Balanced085Data
import BalancedGraphChecks
import LookupCover

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Shared89
open Snake9.Boxes88 Snake9.Certificate88 Snake9.Balanced89

theorem boxTable085_valid : check boxTable085 = true := by decide +kernel

theorem boxTable085_flat : flatten boxTable085 = boxes085 := by decide +kernel

theorem balancedCover085 :
    checkCoverLookup advanceBalanced 614 (fun i => lookup boxTable085 i [])
      6 [] root085 tree085 = true := by decide +kernel

theorem originalCover085 :
    checkCover retainedDiagram boxes085 6 [] root085 tree085 = true := by
  apply lookup_cover_to_original advanceBalanced 614 (fun i => lookup boxTable085 i [])
    retainedDiagram boxes085 root085 tree085
  · decide +kernel
  · intro i
    exact lookup_eq_list boxTable085 boxes085 boxTable085_valid boxTable085_flat i []
  · exact advanceBalanced_eq
  · exact balancedCover085

#print axioms boxTable085_valid
#print axioms boxTable085_flat
#print axioms balancedCover085
#print axioms originalCover085

end Snake9.Shared89
