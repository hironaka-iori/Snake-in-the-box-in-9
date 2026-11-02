import Balanced108Data
import BalancedGraphChecks
import LookupCover

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Shared89
open Snake9.Boxes88 Snake9.Certificate88 Snake9.Balanced89

theorem boxTable108_valid : check boxTable108 = true := by decide +kernel

theorem boxTable108_flat : flatten boxTable108 = boxes108 := by decide +kernel

theorem balancedCover108 :
    checkCoverLookup advanceBalanced 302 (fun i => lookup boxTable108 i [])
      6 [] root108 tree108 = true := by decide +kernel

theorem originalCover108 :
    checkCover retainedDiagram boxes108 6 [] root108 tree108 = true := by
  apply lookup_cover_to_original advanceBalanced 302 (fun i => lookup boxTable108 i [])
    retainedDiagram boxes108 root108 tree108
  · decide +kernel
  · intro i
    exact lookup_eq_list boxTable108 boxes108 boxTable108_valid boxTable108_flat i []
  · exact advanceBalanced_eq
  · exact balancedCover108

#print axioms boxTable108_valid
#print axioms boxTable108_flat
#print axioms balancedCover108
#print axioms originalCover108

end Snake9.Shared89
