import Balanced086Data
import BalancedGraphChecks
import LookupCover

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Shared89
open Snake9.Boxes88 Snake9.Certificate88 Snake9.Balanced89

theorem boxTable086_valid : check boxTable086 = true := by decide +kernel

theorem boxTable086_flat : flatten boxTable086 = boxes086 := by decide +kernel

theorem balancedCover086 :
    checkCoverLookup advanceBalanced 921 (fun i => lookup boxTable086 i [])
      6 [] root086 tree086 = true := by decide +kernel

theorem originalCover086 :
    checkCover retainedDiagram boxes086 6 [] root086 tree086 = true := by
  apply lookup_cover_to_original advanceBalanced 921 (fun i => lookup boxTable086 i [])
    retainedDiagram boxes086 root086 tree086
  · decide +kernel
  · intro i
    exact lookup_eq_list boxTable086 boxes086 boxTable086_valid boxTable086_flat i []
  · exact advanceBalanced_eq
  · exact balancedCover086

#print axioms boxTable086_valid
#print axioms boxTable086_flat
#print axioms balancedCover086
#print axioms originalCover086

end Snake9.Shared89
