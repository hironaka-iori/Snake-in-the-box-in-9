import Balanced103Data
import BalancedGraphChecks
import LookupCover

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Shared89
open Snake9.Boxes88 Snake9.Certificate88 Snake9.Balanced89

theorem boxTable103_valid : check boxTable103 = true := by decide +kernel

theorem boxTable103_flat : flatten boxTable103 = boxes103 := by decide +kernel

theorem balancedCover103 :
    checkCoverLookup advanceBalanced 859 (fun i => lookup boxTable103 i [])
      6 [] root103 tree103 = true := by decide +kernel

theorem originalCover103 :
    checkCover retainedDiagram boxes103 6 [] root103 tree103 = true := by
  apply lookup_cover_to_original advanceBalanced 859 (fun i => lookup boxTable103 i [])
    retainedDiagram boxes103 root103 tree103
  · decide +kernel
  · intro i
    exact lookup_eq_list boxTable103 boxes103 boxTable103_valid boxTable103_flat i []
  · exact advanceBalanced_eq
  · exact balancedCover103

#print axioms boxTable103_valid
#print axioms boxTable103_flat
#print axioms balancedCover103
#print axioms originalCover103

end Snake9.Shared89
