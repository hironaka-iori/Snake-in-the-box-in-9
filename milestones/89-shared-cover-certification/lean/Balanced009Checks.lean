import Balanced009Data
import BalancedGraphChecks
import LookupCover

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Shared89
open Snake9.Boxes88 Snake9.Certificate88 Snake9.Balanced89

theorem boxTable009_valid : check boxTable009 = true := by decide +kernel

theorem boxTable009_flat : flatten boxTable009 = boxes009 := by decide +kernel

theorem balancedCover009 :
    checkCoverLookup advanceBalanced 393 (fun i => lookup boxTable009 i [])
      6 [] root009 tree009 = true := by decide +kernel

theorem originalCover009 :
    checkCover retainedDiagram boxes009 6 [] root009 tree009 = true := by
  apply lookup_cover_to_original advanceBalanced 393 (fun i => lookup boxTable009 i [])
    retainedDiagram boxes009 root009 tree009
  · decide +kernel
  · intro i
    exact lookup_eq_list boxTable009 boxes009 boxTable009_valid boxTable009_flat i []
  · exact advanceBalanced_eq
  · exact balancedCover009

#print axioms boxTable009_valid
#print axioms boxTable009_flat
#print axioms balancedCover009
#print axioms originalCover009

end Snake9.Shared89
