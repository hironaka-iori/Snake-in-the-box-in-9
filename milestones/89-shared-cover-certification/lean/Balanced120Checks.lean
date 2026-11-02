import Balanced120Data
import BalancedGraphChecks
import LookupCover

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Shared89
open Snake9.Boxes88 Snake9.Certificate88 Snake9.Balanced89

theorem boxTable120_valid : check boxTable120 = true := by decide +kernel

theorem boxTable120_flat : flatten boxTable120 = boxes120 := by decide +kernel

theorem balancedCover120 :
    checkCoverLookup advanceBalanced 416 (fun i => lookup boxTable120 i [])
      6 [] root120 tree120 = true := by decide +kernel

theorem originalCover120 :
    checkCover retainedDiagram boxes120 6 [] root120 tree120 = true := by
  apply lookup_cover_to_original advanceBalanced 416 (fun i => lookup boxTable120 i [])
    retainedDiagram boxes120 root120 tree120
  · decide +kernel
  · intro i
    exact lookup_eq_list boxTable120 boxes120 boxTable120_valid boxTable120_flat i []
  · exact advanceBalanced_eq
  · exact balancedCover120

#print axioms boxTable120_valid
#print axioms boxTable120_flat
#print axioms balancedCover120
#print axioms originalCover120

end Snake9.Shared89
