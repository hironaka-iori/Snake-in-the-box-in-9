import Balanced022Data
import BalancedGraphChecks
import LookupCover

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Shared89
open Snake9.Boxes88 Snake9.Certificate88 Snake9.Balanced89

theorem boxTable022_valid : check boxTable022 = true := by decide +kernel

theorem boxTable022_flat : flatten boxTable022 = boxes022 := by decide +kernel

theorem balancedCover022 :
    checkCoverLookup advanceBalanced 610 (fun i => lookup boxTable022 i [])
      6 [] root022 tree022 = true := by decide +kernel

theorem originalCover022 :
    checkCover retainedDiagram boxes022 6 [] root022 tree022 = true := by
  apply lookup_cover_to_original advanceBalanced 610 (fun i => lookup boxTable022 i [])
    retainedDiagram boxes022 root022 tree022
  · decide +kernel
  · intro i
    exact lookup_eq_list boxTable022 boxes022 boxTable022_valid boxTable022_flat i []
  · exact advanceBalanced_eq
  · exact balancedCover022

#print axioms boxTable022_valid
#print axioms boxTable022_flat
#print axioms balancedCover022
#print axioms originalCover022

end Snake9.Shared89
