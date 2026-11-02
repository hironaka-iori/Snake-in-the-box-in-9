import Balanced016Data
import BalancedGraphChecks
import LookupCover

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Shared89
open Snake9.Boxes88 Snake9.Certificate88 Snake9.Balanced89

theorem boxTable016_valid : check boxTable016 = true := by decide +kernel

theorem boxTable016_flat : flatten boxTable016 = boxes016 := by decide +kernel

theorem balancedCover016 :
    checkCoverLookup advanceBalanced 389 (fun i => lookup boxTable016 i [])
      6 [] root016 tree016 = true := by decide +kernel

theorem originalCover016 :
    checkCover retainedDiagram boxes016 6 [] root016 tree016 = true := by
  apply lookup_cover_to_original advanceBalanced 389 (fun i => lookup boxTable016 i [])
    retainedDiagram boxes016 root016 tree016
  · decide +kernel
  · intro i
    exact lookup_eq_list boxTable016 boxes016 boxTable016_valid boxTable016_flat i []
  · exact advanceBalanced_eq
  · exact balancedCover016

#print axioms boxTable016_valid
#print axioms boxTable016_flat
#print axioms balancedCover016
#print axioms originalCover016

end Snake9.Shared89
