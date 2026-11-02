import Balanced105Data
import BalancedGraphChecks
import LookupCover

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Shared89
open Snake9.Boxes88 Snake9.Certificate88 Snake9.Balanced89

theorem boxTable105_valid : check boxTable105 = true := by decide +kernel

theorem boxTable105_flat : flatten boxTable105 = boxes105 := by decide +kernel

theorem balancedCover105 :
    checkCoverLookup advanceBalanced 681 (fun i => lookup boxTable105 i [])
      6 [] root105 tree105 = true := by decide +kernel

theorem originalCover105 :
    checkCover retainedDiagram boxes105 6 [] root105 tree105 = true := by
  apply lookup_cover_to_original advanceBalanced 681 (fun i => lookup boxTable105 i [])
    retainedDiagram boxes105 root105 tree105
  · decide +kernel
  · intro i
    exact lookup_eq_list boxTable105 boxes105 boxTable105_valid boxTable105_flat i []
  · exact advanceBalanced_eq
  · exact balancedCover105

#print axioms boxTable105_valid
#print axioms boxTable105_flat
#print axioms balancedCover105
#print axioms originalCover105

end Snake9.Shared89
