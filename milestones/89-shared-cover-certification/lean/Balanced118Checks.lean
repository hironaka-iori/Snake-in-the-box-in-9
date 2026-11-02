import Balanced118Data
import BalancedGraphChecks
import LookupCover

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Shared89
open Snake9.Boxes88 Snake9.Certificate88 Snake9.Balanced89

theorem boxTable118_valid : check boxTable118 = true := by decide +kernel

theorem boxTable118_flat : flatten boxTable118 = boxes118 := by decide +kernel

theorem balancedCover118 :
    checkCoverLookup advanceBalanced 341 (fun i => lookup boxTable118 i [])
      6 [] root118 tree118 = true := by decide +kernel

theorem originalCover118 :
    checkCover retainedDiagram boxes118 6 [] root118 tree118 = true := by
  apply lookup_cover_to_original advanceBalanced 341 (fun i => lookup boxTable118 i [])
    retainedDiagram boxes118 root118 tree118
  · decide +kernel
  · intro i
    exact lookup_eq_list boxTable118 boxes118 boxTable118_valid boxTable118_flat i []
  · exact advanceBalanced_eq
  · exact balancedCover118

#print axioms boxTable118_valid
#print axioms boxTable118_flat
#print axioms balancedCover118
#print axioms originalCover118

end Snake9.Shared89
