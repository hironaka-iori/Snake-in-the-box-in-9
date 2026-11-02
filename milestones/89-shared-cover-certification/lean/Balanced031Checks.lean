import Balanced031Data
import BalancedGraphChecks
import LookupCover

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Shared89
open Snake9.Boxes88 Snake9.Certificate88 Snake9.Balanced89

theorem boxTable031_valid : check boxTable031 = true := by decide +kernel

theorem boxTable031_flat : flatten boxTable031 = boxes031 := by decide +kernel

theorem balancedCover031 :
    checkCoverLookup advanceBalanced 413 (fun i => lookup boxTable031 i [])
      6 [] root031 tree031 = true := by decide +kernel

theorem originalCover031 :
    checkCover retainedDiagram boxes031 6 [] root031 tree031 = true := by
  apply lookup_cover_to_original advanceBalanced 413 (fun i => lookup boxTable031 i [])
    retainedDiagram boxes031 root031 tree031
  · decide +kernel
  · intro i
    exact lookup_eq_list boxTable031 boxes031 boxTable031_valid boxTable031_flat i []
  · exact advanceBalanced_eq
  · exact balancedCover031

#print axioms boxTable031_valid
#print axioms boxTable031_flat
#print axioms balancedCover031
#print axioms originalCover031

end Snake9.Shared89
