import Balanced049Data
import BalancedGraphChecks
import LookupCover

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Shared89
open Snake9.Boxes88 Snake9.Certificate88 Snake9.Balanced89

theorem boxTable049_valid : check boxTable049 = true := by decide +kernel

theorem boxTable049_flat : flatten boxTable049 = boxes049 := by decide +kernel

theorem balancedCover049 :
    checkCoverLookup advanceBalanced 386 (fun i => lookup boxTable049 i [])
      6 [] root049 tree049 = true := by decide +kernel

theorem originalCover049 :
    checkCover retainedDiagram boxes049 6 [] root049 tree049 = true := by
  apply lookup_cover_to_original advanceBalanced 386 (fun i => lookup boxTable049 i [])
    retainedDiagram boxes049 root049 tree049
  · decide +kernel
  · intro i
    exact lookup_eq_list boxTable049 boxes049 boxTable049_valid boxTable049_flat i []
  · exact advanceBalanced_eq
  · exact balancedCover049

#print axioms boxTable049_valid
#print axioms boxTable049_flat
#print axioms balancedCover049
#print axioms originalCover049

end Snake9.Shared89
