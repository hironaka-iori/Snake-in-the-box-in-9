import Balanced055Data
import BalancedGraphChecks
import LookupCover

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Shared89
open Snake9.Boxes88 Snake9.Certificate88 Snake9.Balanced89

theorem boxTable055_valid : check boxTable055 = true := by decide +kernel

theorem boxTable055_flat : flatten boxTable055 = boxes055 := by decide +kernel

theorem balancedCover055 :
    checkCoverLookup advanceBalanced 790 (fun i => lookup boxTable055 i [])
      6 [] root055 tree055 = true := by decide +kernel

theorem originalCover055 :
    checkCover retainedDiagram boxes055 6 [] root055 tree055 = true := by
  apply lookup_cover_to_original advanceBalanced 790 (fun i => lookup boxTable055 i [])
    retainedDiagram boxes055 root055 tree055
  · decide +kernel
  · intro i
    exact lookup_eq_list boxTable055 boxes055 boxTable055_valid boxTable055_flat i []
  · exact advanceBalanced_eq
  · exact balancedCover055

#print axioms boxTable055_valid
#print axioms boxTable055_flat
#print axioms balancedCover055
#print axioms originalCover055

end Snake9.Shared89
