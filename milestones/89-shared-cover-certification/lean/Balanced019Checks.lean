import Balanced019Data
import BalancedGraphChecks
import LookupCover

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Shared89
open Snake9.Boxes88 Snake9.Certificate88 Snake9.Balanced89

theorem boxTable019_valid : check boxTable019 = true := by decide +kernel

theorem boxTable019_flat : flatten boxTable019 = boxes019 := by decide +kernel

theorem balancedCover019 :
    checkCoverLookup advanceBalanced 692 (fun i => lookup boxTable019 i [])
      6 [] root019 tree019 = true := by decide +kernel

theorem originalCover019 :
    checkCover retainedDiagram boxes019 6 [] root019 tree019 = true := by
  apply lookup_cover_to_original advanceBalanced 692 (fun i => lookup boxTable019 i [])
    retainedDiagram boxes019 root019 tree019
  · decide +kernel
  · intro i
    exact lookup_eq_list boxTable019 boxes019 boxTable019_valid boxTable019_flat i []
  · exact advanceBalanced_eq
  · exact balancedCover019

#print axioms boxTable019_valid
#print axioms boxTable019_flat
#print axioms balancedCover019
#print axioms originalCover019

end Snake9.Shared89
