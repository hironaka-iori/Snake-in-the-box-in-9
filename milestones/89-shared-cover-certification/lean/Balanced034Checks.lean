import Balanced034Data
import BalancedGraphChecks
import LookupCover

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Shared89
open Snake9.Boxes88 Snake9.Certificate88 Snake9.Balanced89

theorem boxTable034_valid : check boxTable034 = true := by decide +kernel

theorem boxTable034_flat : flatten boxTable034 = boxes034 := by decide +kernel

theorem balancedCover034 :
    checkCoverLookup advanceBalanced 872 (fun i => lookup boxTable034 i [])
      6 [] root034 tree034 = true := by decide +kernel

theorem originalCover034 :
    checkCover retainedDiagram boxes034 6 [] root034 tree034 = true := by
  apply lookup_cover_to_original advanceBalanced 872 (fun i => lookup boxTable034 i [])
    retainedDiagram boxes034 root034 tree034
  · decide +kernel
  · intro i
    exact lookup_eq_list boxTable034 boxes034 boxTable034_valid boxTable034_flat i []
  · exact advanceBalanced_eq
  · exact balancedCover034

#print axioms boxTable034_valid
#print axioms boxTable034_flat
#print axioms balancedCover034
#print axioms originalCover034

end Snake9.Shared89
