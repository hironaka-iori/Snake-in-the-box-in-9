import Balanced099Data
import BalancedGraphChecks
import LookupCover

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Shared89
open Snake9.Boxes88 Snake9.Certificate88 Snake9.Balanced89

theorem boxTable099_valid : check boxTable099 = true := by decide +kernel

theorem boxTable099_flat : flatten boxTable099 = boxes099 := by decide +kernel

theorem balancedCover099 :
    checkCoverLookup advanceBalanced 863 (fun i => lookup boxTable099 i [])
      6 [] root099 tree099 = true := by decide +kernel

theorem originalCover099 :
    checkCover retainedDiagram boxes099 6 [] root099 tree099 = true := by
  apply lookup_cover_to_original advanceBalanced 863 (fun i => lookup boxTable099 i [])
    retainedDiagram boxes099 root099 tree099
  · decide +kernel
  · intro i
    exact lookup_eq_list boxTable099 boxes099 boxTable099_valid boxTable099_flat i []
  · exact advanceBalanced_eq
  · exact balancedCover099

#print axioms boxTable099_valid
#print axioms boxTable099_flat
#print axioms balancedCover099
#print axioms originalCover099

end Snake9.Shared89
