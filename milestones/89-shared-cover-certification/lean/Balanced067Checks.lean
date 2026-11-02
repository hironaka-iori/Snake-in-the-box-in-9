import Balanced067Data
import BalancedGraphChecks
import LookupCover

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Shared89
open Snake9.Boxes88 Snake9.Certificate88 Snake9.Balanced89

theorem boxTable067_valid : check boxTable067 = true := by decide +kernel

theorem boxTable067_flat : flatten boxTable067 = boxes067 := by decide +kernel

theorem balancedCover067 :
    checkCoverLookup advanceBalanced 620 (fun i => lookup boxTable067 i [])
      6 [] root067 tree067 = true := by decide +kernel

theorem originalCover067 :
    checkCover retainedDiagram boxes067 6 [] root067 tree067 = true := by
  apply lookup_cover_to_original advanceBalanced 620 (fun i => lookup boxTable067 i [])
    retainedDiagram boxes067 root067 tree067
  · decide +kernel
  · intro i
    exact lookup_eq_list boxTable067 boxes067 boxTable067_valid boxTable067_flat i []
  · exact advanceBalanced_eq
  · exact balancedCover067

#print axioms boxTable067_valid
#print axioms boxTable067_flat
#print axioms balancedCover067
#print axioms originalCover067

end Snake9.Shared89
