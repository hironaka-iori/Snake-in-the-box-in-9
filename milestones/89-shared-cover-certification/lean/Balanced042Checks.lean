import Balanced042Data
import BalancedGraphChecks
import LookupCover

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Shared89
open Snake9.Boxes88 Snake9.Certificate88 Snake9.Balanced89

theorem boxTable042_valid : check boxTable042 = true := by decide +kernel

theorem boxTable042_flat : flatten boxTable042 = boxes042 := by decide +kernel

theorem balancedCover042 :
    checkCoverLookup advanceBalanced 729 (fun i => lookup boxTable042 i [])
      6 [] root042 tree042 = true := by decide +kernel

theorem originalCover042 :
    checkCover retainedDiagram boxes042 6 [] root042 tree042 = true := by
  apply lookup_cover_to_original advanceBalanced 729 (fun i => lookup boxTable042 i [])
    retainedDiagram boxes042 root042 tree042
  · decide +kernel
  · intro i
    exact lookup_eq_list boxTable042 boxes042 boxTable042_valid boxTable042_flat i []
  · exact advanceBalanced_eq
  · exact balancedCover042

#print axioms boxTable042_valid
#print axioms boxTable042_flat
#print axioms balancedCover042
#print axioms originalCover042

end Snake9.Shared89
