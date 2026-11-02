import Balanced004Data
import BalancedGraphChecks
import LookupCover

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Shared89
open Snake9.Boxes88 Snake9.Certificate88 Snake9.Balanced89

theorem boxTable004_valid : check boxTable004 = true := by decide +kernel

theorem boxTable004_flat : flatten boxTable004 = boxes004 := by decide +kernel

theorem balancedCover004 :
    checkCoverLookup advanceBalanced 913 (fun i => lookup boxTable004 i [])
      6 [] root004 tree004 = true := by decide +kernel

theorem originalCover004 :
    checkCover retainedDiagram boxes004 6 [] root004 tree004 = true := by
  apply lookup_cover_to_original advanceBalanced 913 (fun i => lookup boxTable004 i [])
    retainedDiagram boxes004 root004 tree004
  · decide +kernel
  · intro i
    exact lookup_eq_list boxTable004 boxes004 boxTable004_valid boxTable004_flat i []
  · exact advanceBalanced_eq
  · exact balancedCover004

#print axioms boxTable004_valid
#print axioms boxTable004_flat
#print axioms balancedCover004
#print axioms originalCover004

end Snake9.Shared89
