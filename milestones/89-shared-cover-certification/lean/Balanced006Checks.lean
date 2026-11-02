import Balanced006Data
import BalancedGraphChecks
import LookupCover

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Shared89
open Snake9.Boxes88 Snake9.Certificate88 Snake9.Balanced89

theorem boxTable006_valid : check boxTable006 = true := by decide +kernel

theorem boxTable006_flat : flatten boxTable006 = boxes006 := by decide +kernel

theorem balancedCover006 :
    checkCoverLookup advanceBalanced 722 (fun i => lookup boxTable006 i [])
      6 [] root006 tree006 = true := by decide +kernel

theorem originalCover006 :
    checkCover retainedDiagram boxes006 6 [] root006 tree006 = true := by
  apply lookup_cover_to_original advanceBalanced 722 (fun i => lookup boxTable006 i [])
    retainedDiagram boxes006 root006 tree006
  · decide +kernel
  · intro i
    exact lookup_eq_list boxTable006 boxes006 boxTable006_valid boxTable006_flat i []
  · exact advanceBalanced_eq
  · exact balancedCover006

#print axioms boxTable006_valid
#print axioms boxTable006_flat
#print axioms balancedCover006
#print axioms originalCover006

end Snake9.Shared89
