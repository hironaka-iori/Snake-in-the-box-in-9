import Balanced011Data
import BalancedGraphChecks
import LookupCover

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Shared89
open Snake9.Boxes88 Snake9.Certificate88 Snake9.Balanced89

theorem boxTable011_valid : check boxTable011 = true := by decide +kernel

theorem boxTable011_flat : flatten boxTable011 = boxes011 := by decide +kernel

theorem balancedCover011 :
    checkCoverLookup advanceBalanced 776 (fun i => lookup boxTable011 i [])
      6 [] root011 tree011 = true := by decide +kernel

theorem originalCover011 :
    checkCover retainedDiagram boxes011 6 [] root011 tree011 = true := by
  apply lookup_cover_to_original advanceBalanced 776 (fun i => lookup boxTable011 i [])
    retainedDiagram boxes011 root011 tree011
  · decide +kernel
  · intro i
    exact lookup_eq_list boxTable011 boxes011 boxTable011_valid boxTable011_flat i []
  · exact advanceBalanced_eq
  · exact balancedCover011

#print axioms boxTable011_valid
#print axioms boxTable011_flat
#print axioms balancedCover011
#print axioms originalCover011

end Snake9.Shared89
