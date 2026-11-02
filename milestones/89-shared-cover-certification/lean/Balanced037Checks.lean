import Balanced037Data
import BalancedGraphChecks
import LookupCover

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Shared89
open Snake9.Boxes88 Snake9.Certificate88 Snake9.Balanced89

theorem boxTable037_valid : check boxTable037 = true := by decide +kernel

theorem boxTable037_flat : flatten boxTable037 = boxes037 := by decide +kernel

theorem balancedCover037 :
    checkCoverLookup advanceBalanced 784 (fun i => lookup boxTable037 i [])
      6 [] root037 tree037 = true := by decide +kernel

theorem originalCover037 :
    checkCover retainedDiagram boxes037 6 [] root037 tree037 = true := by
  apply lookup_cover_to_original advanceBalanced 784 (fun i => lookup boxTable037 i [])
    retainedDiagram boxes037 root037 tree037
  · decide +kernel
  · intro i
    exact lookup_eq_list boxTable037 boxes037 boxTable037_valid boxTable037_flat i []
  · exact advanceBalanced_eq
  · exact balancedCover037

#print axioms boxTable037_valid
#print axioms boxTable037_flat
#print axioms balancedCover037
#print axioms originalCover037

end Snake9.Shared89
