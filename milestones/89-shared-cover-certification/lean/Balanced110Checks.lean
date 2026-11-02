import Balanced110Data
import BalancedGraphChecks
import LookupCover

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Shared89
open Snake9.Boxes88 Snake9.Certificate88 Snake9.Balanced89

theorem boxTable110_valid : check boxTable110 = true := by decide +kernel

theorem boxTable110_flat : flatten boxTable110 = boxes110 := by decide +kernel

theorem balancedCover110 :
    checkCoverLookup advanceBalanced 623 (fun i => lookup boxTable110 i [])
      6 [] root110 tree110 = true := by decide +kernel

theorem originalCover110 :
    checkCover retainedDiagram boxes110 6 [] root110 tree110 = true := by
  apply lookup_cover_to_original advanceBalanced 623 (fun i => lookup boxTable110 i [])
    retainedDiagram boxes110 root110 tree110
  · decide +kernel
  · intro i
    exact lookup_eq_list boxTable110 boxes110 boxTable110_valid boxTable110_flat i []
  · exact advanceBalanced_eq
  · exact balancedCover110

#print axioms boxTable110_valid
#print axioms boxTable110_flat
#print axioms balancedCover110
#print axioms originalCover110

end Snake9.Shared89
