import Balanced125Data
import BalancedGraphChecks
import LookupCover

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Shared89
open Snake9.Boxes88 Snake9.Certificate88 Snake9.Balanced89

theorem boxTable125_valid : check boxTable125 = true := by decide +kernel

theorem boxTable125_flat : flatten boxTable125 = boxes125 := by decide +kernel

theorem balancedCover125 :
    checkCoverLookup advanceBalanced 645 (fun i => lookup boxTable125 i [])
      6 [] root125 tree125 = true := by decide +kernel

theorem originalCover125 :
    checkCover retainedDiagram boxes125 6 [] root125 tree125 = true := by
  apply lookup_cover_to_original advanceBalanced 645 (fun i => lookup boxTable125 i [])
    retainedDiagram boxes125 root125 tree125
  · decide +kernel
  · intro i
    exact lookup_eq_list boxTable125 boxes125 boxTable125_valid boxTable125_flat i []
  · exact advanceBalanced_eq
  · exact balancedCover125

#print axioms boxTable125_valid
#print axioms boxTable125_flat
#print axioms balancedCover125
#print axioms originalCover125

end Snake9.Shared89
