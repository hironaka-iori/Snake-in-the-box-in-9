import Balanced068Data
import BalancedGraphChecks
import LookupCover

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Shared89
open Snake9.Boxes88 Snake9.Certificate88 Snake9.Balanced89

theorem boxTable068_valid : check boxTable068 = true := by decide +kernel

theorem boxTable068_flat : flatten boxTable068 = boxes068 := by decide +kernel

theorem balancedCover068 :
    checkCoverLookup advanceBalanced 470 (fun i => lookup boxTable068 i [])
      6 [] root068 tree068 = true := by decide +kernel

theorem originalCover068 :
    checkCover retainedDiagram boxes068 6 [] root068 tree068 = true := by
  apply lookup_cover_to_original advanceBalanced 470 (fun i => lookup boxTable068 i [])
    retainedDiagram boxes068 root068 tree068
  · decide +kernel
  · intro i
    exact lookup_eq_list boxTable068 boxes068 boxTable068_valid boxTable068_flat i []
  · exact advanceBalanced_eq
  · exact balancedCover068

#print axioms boxTable068_valid
#print axioms boxTable068_flat
#print axioms balancedCover068
#print axioms originalCover068

end Snake9.Shared89
