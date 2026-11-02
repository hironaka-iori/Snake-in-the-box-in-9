import Balanced001Data
import BalancedGraphChecks
import LookupCover

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Shared89
open Snake9.Boxes88 Snake9.Certificate88 Snake9.Balanced89

theorem boxTable001_valid : check boxTable001 = true := by decide +kernel

theorem boxTable001_flat : flatten boxTable001 = boxes001 := by decide +kernel

theorem balancedCover001 :
    checkCoverLookup advanceBalanced 640 (fun i => lookup boxTable001 i [])
      6 [] root001 tree001 = true := by decide +kernel

theorem originalCover001 :
    checkCover retainedDiagram boxes001 6 [] root001 tree001 = true := by
  apply lookup_cover_to_original advanceBalanced 640 (fun i => lookup boxTable001 i [])
    retainedDiagram boxes001 root001 tree001
  · decide +kernel
  · intro i
    exact lookup_eq_list boxTable001 boxes001 boxTable001_valid boxTable001_flat i []
  · exact advanceBalanced_eq
  · exact balancedCover001

#print axioms boxTable001_valid
#print axioms boxTable001_flat
#print axioms balancedCover001
#print axioms originalCover001

end Snake9.Shared89
