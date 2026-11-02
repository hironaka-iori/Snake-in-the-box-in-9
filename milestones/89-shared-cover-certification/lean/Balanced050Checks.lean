import Balanced050Data
import BalancedGraphChecks
import LookupCover

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Shared89
open Snake9.Boxes88 Snake9.Certificate88 Snake9.Balanced89

theorem boxTable050_valid : check boxTable050 = true := by decide +kernel

theorem boxTable050_flat : flatten boxTable050 = boxes050 := by decide +kernel

theorem balancedCover050 :
    checkCoverLookup advanceBalanced 684 (fun i => lookup boxTable050 i [])
      6 [] root050 tree050 = true := by decide +kernel

theorem originalCover050 :
    checkCover retainedDiagram boxes050 6 [] root050 tree050 = true := by
  apply lookup_cover_to_original advanceBalanced 684 (fun i => lookup boxTable050 i [])
    retainedDiagram boxes050 root050 tree050
  · decide +kernel
  · intro i
    exact lookup_eq_list boxTable050 boxes050 boxTable050_valid boxTable050_flat i []
  · exact advanceBalanced_eq
  · exact balancedCover050

#print axioms boxTable050_valid
#print axioms boxTable050_flat
#print axioms balancedCover050
#print axioms originalCover050

end Snake9.Shared89
