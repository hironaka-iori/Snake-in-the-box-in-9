import Balanced028Data
import BalancedGraphChecks
import LookupCover

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Shared89
open Snake9.Boxes88 Snake9.Certificate88 Snake9.Balanced89

theorem boxTable028_valid : check boxTable028 = true := by decide +kernel

theorem boxTable028_flat : flatten boxTable028 = boxes028 := by decide +kernel

theorem balancedCover028 :
    checkCoverLookup advanceBalanced 667 (fun i => lookup boxTable028 i [])
      6 [] root028 tree028 = true := by decide +kernel

theorem originalCover028 :
    checkCover retainedDiagram boxes028 6 [] root028 tree028 = true := by
  apply lookup_cover_to_original advanceBalanced 667 (fun i => lookup boxTable028 i [])
    retainedDiagram boxes028 root028 tree028
  · decide +kernel
  · intro i
    exact lookup_eq_list boxTable028 boxes028 boxTable028_valid boxTable028_flat i []
  · exact advanceBalanced_eq
  · exact balancedCover028

#print axioms boxTable028_valid
#print axioms boxTable028_flat
#print axioms balancedCover028
#print axioms originalCover028

end Snake9.Shared89
