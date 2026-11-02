import Balanced053Data
import BalancedGraphChecks
import LookupCover

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Shared89
open Snake9.Boxes88 Snake9.Certificate88 Snake9.Balanced89

theorem boxTable053_valid : check boxTable053 = true := by decide +kernel

theorem boxTable053_flat : flatten boxTable053 = boxes053 := by decide +kernel

theorem balancedCover053 :
    checkCoverLookup advanceBalanced 376 (fun i => lookup boxTable053 i [])
      6 [] root053 tree053 = true := by decide +kernel

theorem originalCover053 :
    checkCover retainedDiagram boxes053 6 [] root053 tree053 = true := by
  apply lookup_cover_to_original advanceBalanced 376 (fun i => lookup boxTable053 i [])
    retainedDiagram boxes053 root053 tree053
  · decide +kernel
  · intro i
    exact lookup_eq_list boxTable053 boxes053 boxTable053_valid boxTable053_flat i []
  · exact advanceBalanced_eq
  · exact balancedCover053

#print axioms boxTable053_valid
#print axioms boxTable053_flat
#print axioms balancedCover053
#print axioms originalCover053

end Snake9.Shared89
