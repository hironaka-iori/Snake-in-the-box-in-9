import Balanced080Data
import BalancedGraphChecks
import LookupCover

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Shared89
open Snake9.Boxes88 Snake9.Certificate88 Snake9.Balanced89

theorem boxTable080_valid : check boxTable080 = true := by decide +kernel

theorem boxTable080_flat : flatten boxTable080 = boxes080 := by decide +kernel

theorem balancedCover080 :
    checkCoverLookup advanceBalanced 592 (fun i => lookup boxTable080 i [])
      6 [] root080 tree080 = true := by decide +kernel

theorem originalCover080 :
    checkCover retainedDiagram boxes080 6 [] root080 tree080 = true := by
  apply lookup_cover_to_original advanceBalanced 592 (fun i => lookup boxTable080 i [])
    retainedDiagram boxes080 root080 tree080
  · decide +kernel
  · intro i
    exact lookup_eq_list boxTable080 boxes080 boxTable080_valid boxTable080_flat i []
  · exact advanceBalanced_eq
  · exact balancedCover080

#print axioms boxTable080_valid
#print axioms boxTable080_flat
#print axioms balancedCover080
#print axioms originalCover080

end Snake9.Shared89
