import Balanced075Data
import BalancedGraphChecks
import LookupCover

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Shared89
open Snake9.Boxes88 Snake9.Certificate88 Snake9.Balanced89

theorem boxTable075_valid : check boxTable075 = true := by decide +kernel

theorem boxTable075_flat : flatten boxTable075 = boxes075 := by decide +kernel

theorem balancedCover075 :
    checkCoverLookup advanceBalanced 590 (fun i => lookup boxTable075 i [])
      6 [] root075 tree075 = true := by decide +kernel

theorem originalCover075 :
    checkCover retainedDiagram boxes075 6 [] root075 tree075 = true := by
  apply lookup_cover_to_original advanceBalanced 590 (fun i => lookup boxTable075 i [])
    retainedDiagram boxes075 root075 tree075
  · decide +kernel
  · intro i
    exact lookup_eq_list boxTable075 boxes075 boxTable075_valid boxTable075_flat i []
  · exact advanceBalanced_eq
  · exact balancedCover075

#print axioms boxTable075_valid
#print axioms boxTable075_flat
#print axioms balancedCover075
#print axioms originalCover075

end Snake9.Shared89
