import Balanced066Data
import BalancedGraphChecks
import LookupCover

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Shared89
open Snake9.Boxes88 Snake9.Certificate88 Snake9.Balanced89

theorem boxTable066_valid : check boxTable066 = true := by decide +kernel

theorem boxTable066_flat : flatten boxTable066 = boxes066 := by decide +kernel

theorem balancedCover066 :
    checkCoverLookup advanceBalanced 739 (fun i => lookup boxTable066 i [])
      6 [] root066 tree066 = true := by decide +kernel

theorem originalCover066 :
    checkCover retainedDiagram boxes066 6 [] root066 tree066 = true := by
  apply lookup_cover_to_original advanceBalanced 739 (fun i => lookup boxTable066 i [])
    retainedDiagram boxes066 root066 tree066
  · decide +kernel
  · intro i
    exact lookup_eq_list boxTable066 boxes066 boxTable066_valid boxTable066_flat i []
  · exact advanceBalanced_eq
  · exact balancedCover066

#print axioms boxTable066_valid
#print axioms boxTable066_flat
#print axioms balancedCover066
#print axioms originalCover066

end Snake9.Shared89
