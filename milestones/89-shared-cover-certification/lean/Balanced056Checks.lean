import Balanced056Data
import BalancedGraphChecks
import LookupCover

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Shared89
open Snake9.Boxes88 Snake9.Certificate88 Snake9.Balanced89

theorem boxTable056_valid : check boxTable056 = true := by decide +kernel

theorem boxTable056_flat : flatten boxTable056 = boxes056 := by decide +kernel

theorem balancedCover056 :
    checkCoverLookup advanceBalanced 691 (fun i => lookup boxTable056 i [])
      6 [] root056 tree056 = true := by decide +kernel

theorem originalCover056 :
    checkCover retainedDiagram boxes056 6 [] root056 tree056 = true := by
  apply lookup_cover_to_original advanceBalanced 691 (fun i => lookup boxTable056 i [])
    retainedDiagram boxes056 root056 tree056
  · decide +kernel
  · intro i
    exact lookup_eq_list boxTable056 boxes056 boxTable056_valid boxTable056_flat i []
  · exact advanceBalanced_eq
  · exact balancedCover056

#print axioms boxTable056_valid
#print axioms boxTable056_flat
#print axioms balancedCover056
#print axioms originalCover056

end Snake9.Shared89
