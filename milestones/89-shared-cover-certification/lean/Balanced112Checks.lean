import Balanced112Data
import BalancedGraphChecks
import LookupCover

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Shared89
open Snake9.Boxes88 Snake9.Certificate88 Snake9.Balanced89

theorem boxTable112_valid : check boxTable112 = true := by decide +kernel

theorem boxTable112_flat : flatten boxTable112 = boxes112 := by decide +kernel

theorem balancedCover112 :
    checkCoverLookup advanceBalanced 616 (fun i => lookup boxTable112 i [])
      6 [] root112 tree112 = true := by decide +kernel

theorem originalCover112 :
    checkCover retainedDiagram boxes112 6 [] root112 tree112 = true := by
  apply lookup_cover_to_original advanceBalanced 616 (fun i => lookup boxTable112 i [])
    retainedDiagram boxes112 root112 tree112
  · decide +kernel
  · intro i
    exact lookup_eq_list boxTable112 boxes112 boxTable112_valid boxTable112_flat i []
  · exact advanceBalanced_eq
  · exact balancedCover112

#print axioms boxTable112_valid
#print axioms boxTable112_flat
#print axioms balancedCover112
#print axioms originalCover112

end Snake9.Shared89
