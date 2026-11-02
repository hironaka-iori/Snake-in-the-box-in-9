import Balanced083Data
import BalancedGraphChecks
import LookupCover

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Shared89
open Snake9.Boxes88 Snake9.Certificate88 Snake9.Balanced89

theorem boxTable083_valid : check boxTable083 = true := by decide +kernel

theorem boxTable083_flat : flatten boxTable083 = boxes083 := by decide +kernel

theorem balancedCover083 :
    checkCoverLookup advanceBalanced 624 (fun i => lookup boxTable083 i [])
      6 [] root083 tree083 = true := by decide +kernel

theorem originalCover083 :
    checkCover retainedDiagram boxes083 6 [] root083 tree083 = true := by
  apply lookup_cover_to_original advanceBalanced 624 (fun i => lookup boxTable083 i [])
    retainedDiagram boxes083 root083 tree083
  · decide +kernel
  · intro i
    exact lookup_eq_list boxTable083 boxes083 boxTable083_valid boxTable083_flat i []
  · exact advanceBalanced_eq
  · exact balancedCover083

#print axioms boxTable083_valid
#print axioms boxTable083_flat
#print axioms balancedCover083
#print axioms originalCover083

end Snake9.Shared89
