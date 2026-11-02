import Balanced077Data
import BalancedGraphChecks
import LookupCover

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Shared89
open Snake9.Boxes88 Snake9.Certificate88 Snake9.Balanced89

theorem boxTable077_valid : check boxTable077 = true := by decide +kernel

theorem boxTable077_flat : flatten boxTable077 = boxes077 := by decide +kernel

theorem balancedCover077 :
    checkCoverLookup advanceBalanced 656 (fun i => lookup boxTable077 i [])
      6 [] root077 tree077 = true := by decide +kernel

theorem originalCover077 :
    checkCover retainedDiagram boxes077 6 [] root077 tree077 = true := by
  apply lookup_cover_to_original advanceBalanced 656 (fun i => lookup boxTable077 i [])
    retainedDiagram boxes077 root077 tree077
  · decide +kernel
  · intro i
    exact lookup_eq_list boxTable077 boxes077 boxTable077_valid boxTable077_flat i []
  · exact advanceBalanced_eq
  · exact balancedCover077

#print axioms boxTable077_valid
#print axioms boxTable077_flat
#print axioms balancedCover077
#print axioms originalCover077

end Snake9.Shared89
