import Balanced017Data
import BalancedGraphChecks
import LookupCover

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Shared89
open Snake9.Boxes88 Snake9.Certificate88 Snake9.Balanced89

theorem boxTable017_valid : check boxTable017 = true := by decide +kernel

theorem boxTable017_flat : flatten boxTable017 = boxes017 := by decide +kernel

theorem balancedCover017 :
    checkCoverLookup advanceBalanced 636 (fun i => lookup boxTable017 i [])
      6 [] root017 tree017 = true := by decide +kernel

theorem originalCover017 :
    checkCover retainedDiagram boxes017 6 [] root017 tree017 = true := by
  apply lookup_cover_to_original advanceBalanced 636 (fun i => lookup boxTable017 i [])
    retainedDiagram boxes017 root017 tree017
  · decide +kernel
  · intro i
    exact lookup_eq_list boxTable017 boxes017 boxTable017_valid boxTable017_flat i []
  · exact advanceBalanced_eq
  · exact balancedCover017

#print axioms boxTable017_valid
#print axioms boxTable017_flat
#print axioms balancedCover017
#print axioms originalCover017

end Snake9.Shared89
