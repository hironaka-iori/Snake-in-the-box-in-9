import Balanced090Data
import BalancedGraphChecks
import LookupCover

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Shared89
open Snake9.Boxes88 Snake9.Certificate88 Snake9.Balanced89

theorem boxTable090_valid : check boxTable090 = true := by decide +kernel

theorem boxTable090_flat : flatten boxTable090 = boxes090 := by decide +kernel

theorem balancedCover090 :
    checkCoverLookup advanceBalanced 839 (fun i => lookup boxTable090 i [])
      6 [] root090 tree090 = true := by decide +kernel

theorem originalCover090 :
    checkCover retainedDiagram boxes090 6 [] root090 tree090 = true := by
  apply lookup_cover_to_original advanceBalanced 839 (fun i => lookup boxTable090 i [])
    retainedDiagram boxes090 root090 tree090
  · decide +kernel
  · intro i
    exact lookup_eq_list boxTable090 boxes090 boxTable090_valid boxTable090_flat i []
  · exact advanceBalanced_eq
  · exact balancedCover090

#print axioms boxTable090_valid
#print axioms boxTable090_flat
#print axioms balancedCover090
#print axioms originalCover090

end Snake9.Shared89
