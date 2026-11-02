import Balanced038Data
import BalancedGraphChecks
import LookupCover

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Shared89
open Snake9.Boxes88 Snake9.Certificate88 Snake9.Balanced89

theorem boxTable038_valid : check boxTable038 = true := by decide +kernel

theorem boxTable038_flat : flatten boxTable038 = boxes038 := by decide +kernel

theorem balancedCover038 :
    checkCoverLookup advanceBalanced 843 (fun i => lookup boxTable038 i [])
      6 [] root038 tree038 = true := by decide +kernel

theorem originalCover038 :
    checkCover retainedDiagram boxes038 6 [] root038 tree038 = true := by
  apply lookup_cover_to_original advanceBalanced 843 (fun i => lookup boxTable038 i [])
    retainedDiagram boxes038 root038 tree038
  · decide +kernel
  · intro i
    exact lookup_eq_list boxTable038 boxes038 boxTable038_valid boxTable038_flat i []
  · exact advanceBalanced_eq
  · exact balancedCover038

#print axioms boxTable038_valid
#print axioms boxTable038_flat
#print axioms balancedCover038
#print axioms originalCover038

end Snake9.Shared89
