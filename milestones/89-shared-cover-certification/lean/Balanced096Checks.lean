import Balanced096Data
import BalancedGraphChecks
import LookupCover

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Shared89
open Snake9.Boxes88 Snake9.Certificate88 Snake9.Balanced89

theorem boxTable096_valid : check boxTable096 = true := by decide +kernel

theorem boxTable096_flat : flatten boxTable096 = boxes096 := by decide +kernel

theorem balancedCover096 :
    checkCoverLookup advanceBalanced 717 (fun i => lookup boxTable096 i [])
      6 [] root096 tree096 = true := by decide +kernel

theorem originalCover096 :
    checkCover retainedDiagram boxes096 6 [] root096 tree096 = true := by
  apply lookup_cover_to_original advanceBalanced 717 (fun i => lookup boxTable096 i [])
    retainedDiagram boxes096 root096 tree096
  · decide +kernel
  · intro i
    exact lookup_eq_list boxTable096 boxes096 boxTable096_valid boxTable096_flat i []
  · exact advanceBalanced_eq
  · exact balancedCover096

#print axioms boxTable096_valid
#print axioms boxTable096_flat
#print axioms balancedCover096
#print axioms originalCover096

end Snake9.Shared89
