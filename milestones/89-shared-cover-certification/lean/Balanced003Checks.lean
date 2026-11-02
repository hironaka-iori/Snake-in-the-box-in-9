import Balanced003Data
import BalancedGraphChecks
import LookupCover

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Shared89
open Snake9.Boxes88 Snake9.Certificate88 Snake9.Balanced89

theorem boxTable003_valid : check boxTable003 = true := by decide +kernel

theorem boxTable003_flat : flatten boxTable003 = boxes003 := by decide +kernel

theorem balancedCover003 :
    checkCoverLookup advanceBalanced 633 (fun i => lookup boxTable003 i [])
      6 [] root003 tree003 = true := by decide +kernel

theorem originalCover003 :
    checkCover retainedDiagram boxes003 6 [] root003 tree003 = true := by
  apply lookup_cover_to_original advanceBalanced 633 (fun i => lookup boxTable003 i [])
    retainedDiagram boxes003 root003 tree003
  · decide +kernel
  · intro i
    exact lookup_eq_list boxTable003 boxes003 boxTable003_valid boxTable003_flat i []
  · exact advanceBalanced_eq
  · exact balancedCover003

#print axioms boxTable003_valid
#print axioms boxTable003_flat
#print axioms balancedCover003
#print axioms originalCover003

end Snake9.Shared89
