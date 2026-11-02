import Balanced014Data
import BalancedGraphChecks
import LookupCover

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Shared89
open Snake9.Boxes88 Snake9.Certificate88 Snake9.Balanced89

theorem boxTable014_valid : check boxTable014 = true := by decide +kernel

theorem boxTable014_flat : flatten boxTable014 = boxes014 := by decide +kernel

theorem balancedCover014 :
    checkCoverLookup advanceBalanced 848 (fun i => lookup boxTable014 i [])
      6 [] root014 tree014 = true := by decide +kernel

theorem originalCover014 :
    checkCover retainedDiagram boxes014 6 [] root014 tree014 = true := by
  apply lookup_cover_to_original advanceBalanced 848 (fun i => lookup boxTable014 i [])
    retainedDiagram boxes014 root014 tree014
  · decide +kernel
  · intro i
    exact lookup_eq_list boxTable014 boxes014 boxTable014_valid boxTable014_flat i []
  · exact advanceBalanced_eq
  · exact balancedCover014

#print axioms boxTable014_valid
#print axioms boxTable014_flat
#print axioms balancedCover014
#print axioms originalCover014

end Snake9.Shared89
