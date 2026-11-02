import Balanced039Data
import BalancedGraphChecks
import LookupCover

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Shared89
open Snake9.Boxes88 Snake9.Certificate88 Snake9.Balanced89

theorem boxTable039_valid : check boxTable039 = true := by decide +kernel

theorem boxTable039_flat : flatten boxTable039 = boxes039 := by decide +kernel

theorem balancedCover039 :
    checkCoverLookup advanceBalanced 532 (fun i => lookup boxTable039 i [])
      6 [] root039 tree039 = true := by decide +kernel

theorem originalCover039 :
    checkCover retainedDiagram boxes039 6 [] root039 tree039 = true := by
  apply lookup_cover_to_original advanceBalanced 532 (fun i => lookup boxTable039 i [])
    retainedDiagram boxes039 root039 tree039
  · decide +kernel
  · intro i
    exact lookup_eq_list boxTable039 boxes039 boxTable039_valid boxTable039_flat i []
  · exact advanceBalanced_eq
  · exact balancedCover039

#print axioms boxTable039_valid
#print axioms boxTable039_flat
#print axioms balancedCover039
#print axioms originalCover039

end Snake9.Shared89
