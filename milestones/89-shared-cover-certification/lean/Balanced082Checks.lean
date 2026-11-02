import Balanced082Data
import BalancedGraphChecks
import LookupCover

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Shared89
open Snake9.Boxes88 Snake9.Certificate88 Snake9.Balanced89

theorem boxTable082_valid : check boxTable082 = true := by decide +kernel

theorem boxTable082_flat : flatten boxTable082 = boxes082 := by decide +kernel

theorem balancedCover082 :
    checkCoverLookup advanceBalanced 797 (fun i => lookup boxTable082 i [])
      6 [] root082 tree082 = true := by decide +kernel

theorem originalCover082 :
    checkCover retainedDiagram boxes082 6 [] root082 tree082 = true := by
  apply lookup_cover_to_original advanceBalanced 797 (fun i => lookup boxTable082 i [])
    retainedDiagram boxes082 root082 tree082
  · decide +kernel
  · intro i
    exact lookup_eq_list boxTable082 boxes082 boxTable082_valid boxTable082_flat i []
  · exact advanceBalanced_eq
  · exact balancedCover082

#print axioms boxTable082_valid
#print axioms boxTable082_flat
#print axioms balancedCover082
#print axioms originalCover082

end Snake9.Shared89
