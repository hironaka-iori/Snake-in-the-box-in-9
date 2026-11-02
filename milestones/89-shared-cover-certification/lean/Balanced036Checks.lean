import Balanced036Data
import BalancedGraphChecks
import LookupCover

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Shared89
open Snake9.Boxes88 Snake9.Certificate88 Snake9.Balanced89

theorem boxTable036_valid : check boxTable036 = true := by decide +kernel

theorem boxTable036_flat : flatten boxTable036 = boxes036 := by decide +kernel

theorem balancedCover036 :
    checkCoverLookup advanceBalanced 729 (fun i => lookup boxTable036 i [])
      6 [] root036 tree036 = true := by decide +kernel

theorem originalCover036 :
    checkCover retainedDiagram boxes036 6 [] root036 tree036 = true := by
  apply lookup_cover_to_original advanceBalanced 729 (fun i => lookup boxTable036 i [])
    retainedDiagram boxes036 root036 tree036
  · decide +kernel
  · intro i
    exact lookup_eq_list boxTable036 boxes036 boxTable036_valid boxTable036_flat i []
  · exact advanceBalanced_eq
  · exact balancedCover036

#print axioms boxTable036_valid
#print axioms boxTable036_flat
#print axioms balancedCover036
#print axioms originalCover036

end Snake9.Shared89
