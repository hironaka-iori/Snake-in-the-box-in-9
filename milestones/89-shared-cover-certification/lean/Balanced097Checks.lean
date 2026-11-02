import Balanced097Data
import BalancedGraphChecks
import LookupCover

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Shared89
open Snake9.Boxes88 Snake9.Certificate88 Snake9.Balanced89

theorem boxTable097_valid : check boxTable097 = true := by decide +kernel

theorem boxTable097_flat : flatten boxTable097 = boxes097 := by decide +kernel

theorem balancedCover097 :
    checkCoverLookup advanceBalanced 956 (fun i => lookup boxTable097 i [])
      6 [] root097 tree097 = true := by decide +kernel

theorem originalCover097 :
    checkCover retainedDiagram boxes097 6 [] root097 tree097 = true := by
  apply lookup_cover_to_original advanceBalanced 956 (fun i => lookup boxTable097 i [])
    retainedDiagram boxes097 root097 tree097
  · decide +kernel
  · intro i
    exact lookup_eq_list boxTable097 boxes097 boxTable097_valid boxTable097_flat i []
  · exact advanceBalanced_eq
  · exact balancedCover097

#print axioms boxTable097_valid
#print axioms boxTable097_flat
#print axioms balancedCover097
#print axioms originalCover097

end Snake9.Shared89
