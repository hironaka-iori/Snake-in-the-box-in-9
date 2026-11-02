import Balanced107Data
import BalancedGraphChecks
import LookupCover

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Shared89
open Snake9.Boxes88 Snake9.Certificate88 Snake9.Balanced89

theorem boxTable107_valid : check boxTable107 = true := by decide +kernel

theorem boxTable107_flat : flatten boxTable107 = boxes107 := by decide +kernel

theorem balancedCover107 :
    checkCoverLookup advanceBalanced 535 (fun i => lookup boxTable107 i [])
      6 [] root107 tree107 = true := by decide +kernel

theorem originalCover107 :
    checkCover retainedDiagram boxes107 6 [] root107 tree107 = true := by
  apply lookup_cover_to_original advanceBalanced 535 (fun i => lookup boxTable107 i [])
    retainedDiagram boxes107 root107 tree107
  · decide +kernel
  · intro i
    exact lookup_eq_list boxTable107 boxes107 boxTable107_valid boxTable107_flat i []
  · exact advanceBalanced_eq
  · exact balancedCover107

#print axioms boxTable107_valid
#print axioms boxTable107_flat
#print axioms balancedCover107
#print axioms originalCover107

end Snake9.Shared89
