import Balanced018Data
import BalancedGraphChecks
import LookupCover

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Shared89
open Snake9.Boxes88 Snake9.Certificate88 Snake9.Balanced89

theorem boxTable018_valid : check boxTable018 = true := by decide +kernel

theorem boxTable018_flat : flatten boxTable018 = boxes018 := by decide +kernel

theorem balancedCover018 :
    checkCoverLookup advanceBalanced 516 (fun i => lookup boxTable018 i [])
      6 [] root018 tree018 = true := by decide +kernel

theorem originalCover018 :
    checkCover retainedDiagram boxes018 6 [] root018 tree018 = true := by
  apply lookup_cover_to_original advanceBalanced 516 (fun i => lookup boxTable018 i [])
    retainedDiagram boxes018 root018 tree018
  · decide +kernel
  · intro i
    exact lookup_eq_list boxTable018 boxes018 boxTable018_valid boxTable018_flat i []
  · exact advanceBalanced_eq
  · exact balancedCover018

#print axioms boxTable018_valid
#print axioms boxTable018_flat
#print axioms balancedCover018
#print axioms originalCover018

end Snake9.Shared89
