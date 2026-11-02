import Balanced115Data
import BalancedGraphChecks
import LookupCover

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Shared89
open Snake9.Boxes88 Snake9.Certificate88 Snake9.Balanced89

theorem boxTable115_valid : check boxTable115 = true := by decide +kernel

theorem boxTable115_flat : flatten boxTable115 = boxes115 := by decide +kernel

theorem balancedCover115 :
    checkCoverLookup advanceBalanced 652 (fun i => lookup boxTable115 i [])
      6 [] root115 tree115 = true := by decide +kernel

theorem originalCover115 :
    checkCover retainedDiagram boxes115 6 [] root115 tree115 = true := by
  apply lookup_cover_to_original advanceBalanced 652 (fun i => lookup boxTable115 i [])
    retainedDiagram boxes115 root115 tree115
  · decide +kernel
  · intro i
    exact lookup_eq_list boxTable115 boxes115 boxTable115_valid boxTable115_flat i []
  · exact advanceBalanced_eq
  · exact balancedCover115

#print axioms boxTable115_valid
#print axioms boxTable115_flat
#print axioms balancedCover115
#print axioms originalCover115

end Snake9.Shared89
