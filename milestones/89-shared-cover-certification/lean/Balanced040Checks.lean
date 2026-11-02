import Balanced040Data
import BalancedGraphChecks
import LookupCover

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Shared89
open Snake9.Boxes88 Snake9.Certificate88 Snake9.Balanced89

theorem boxTable040_valid : check boxTable040 = true := by decide +kernel

theorem boxTable040_flat : flatten boxTable040 = boxes040 := by decide +kernel

theorem balancedCover040 :
    checkCoverLookup advanceBalanced 844 (fun i => lookup boxTable040 i [])
      6 [] root040 tree040 = true := by decide +kernel

theorem originalCover040 :
    checkCover retainedDiagram boxes040 6 [] root040 tree040 = true := by
  apply lookup_cover_to_original advanceBalanced 844 (fun i => lookup boxTable040 i [])
    retainedDiagram boxes040 root040 tree040
  · decide +kernel
  · intro i
    exact lookup_eq_list boxTable040 boxes040 boxTable040_valid boxTable040_flat i []
  · exact advanceBalanced_eq
  · exact balancedCover040

#print axioms boxTable040_valid
#print axioms boxTable040_flat
#print axioms balancedCover040
#print axioms originalCover040

end Snake9.Shared89
