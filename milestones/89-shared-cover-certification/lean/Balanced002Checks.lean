import Balanced002Data
import BalancedGraphChecks
import LookupCover

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Shared89
open Snake9.Boxes88 Snake9.Certificate88 Snake9.Balanced89

theorem boxTable002_valid : check boxTable002 = true := by decide +kernel

theorem boxTable002_flat : flatten boxTable002 = boxes002 := by decide +kernel

theorem balancedCover002 :
    checkCoverLookup advanceBalanced 511 (fun i => lookup boxTable002 i [])
      6 [] root002 tree002 = true := by decide +kernel

theorem originalCover002 :
    checkCover retainedDiagram boxes002 6 [] root002 tree002 = true := by
  apply lookup_cover_to_original advanceBalanced 511 (fun i => lookup boxTable002 i [])
    retainedDiagram boxes002 root002 tree002
  · decide +kernel
  · intro i
    exact lookup_eq_list boxTable002 boxes002 boxTable002_valid boxTable002_flat i []
  · exact advanceBalanced_eq
  · exact balancedCover002

#print axioms boxTable002_valid
#print axioms boxTable002_flat
#print axioms balancedCover002
#print axioms originalCover002

end Snake9.Shared89
