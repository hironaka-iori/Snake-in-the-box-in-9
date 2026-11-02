import Balanced123Data
import BalancedGraphChecks
import LookupCover

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Shared89
open Snake9.Boxes88 Snake9.Certificate88 Snake9.Balanced89

theorem boxTable123_valid : check boxTable123 = true := by decide +kernel

theorem boxTable123_flat : flatten boxTable123 = boxes123 := by decide +kernel

theorem balancedCover123 :
    checkCoverLookup advanceBalanced 654 (fun i => lookup boxTable123 i [])
      6 [] root123 tree123 = true := by decide +kernel

theorem originalCover123 :
    checkCover retainedDiagram boxes123 6 [] root123 tree123 = true := by
  apply lookup_cover_to_original advanceBalanced 654 (fun i => lookup boxTable123 i [])
    retainedDiagram boxes123 root123 tree123
  · decide +kernel
  · intro i
    exact lookup_eq_list boxTable123 boxes123 boxTable123_valid boxTable123_flat i []
  · exact advanceBalanced_eq
  · exact balancedCover123

#print axioms boxTable123_valid
#print axioms boxTable123_flat
#print axioms balancedCover123
#print axioms originalCover123

end Snake9.Shared89
