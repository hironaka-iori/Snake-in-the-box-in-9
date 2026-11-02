import Balanced063Data
import BalancedGraphChecks
import LookupCover

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Shared89
open Snake9.Boxes88 Snake9.Certificate88 Snake9.Balanced89

theorem boxTable063_valid : check boxTable063 = true := by decide +kernel

theorem boxTable063_flat : flatten boxTable063 = boxes063 := by decide +kernel

theorem balancedCover063 :
    checkCoverLookup advanceBalanced 807 (fun i => lookup boxTable063 i [])
      6 [] root063 tree063 = true := by decide +kernel

theorem originalCover063 :
    checkCover retainedDiagram boxes063 6 [] root063 tree063 = true := by
  apply lookup_cover_to_original advanceBalanced 807 (fun i => lookup boxTable063 i [])
    retainedDiagram boxes063 root063 tree063
  · decide +kernel
  · intro i
    exact lookup_eq_list boxTable063 boxes063 boxTable063_valid boxTable063_flat i []
  · exact advanceBalanced_eq
  · exact balancedCover063

#print axioms boxTable063_valid
#print axioms boxTable063_flat
#print axioms balancedCover063
#print axioms originalCover063

end Snake9.Shared89
