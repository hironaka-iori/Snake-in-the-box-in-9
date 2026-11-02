import Balanced074Data
import BalancedGraphChecks
import LookupCover

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Shared89
open Snake9.Boxes88 Snake9.Certificate88 Snake9.Balanced89

theorem boxTable074_valid : check boxTable074 = true := by decide +kernel

theorem boxTable074_flat : flatten boxTable074 = boxes074 := by decide +kernel

theorem balancedCover074 :
    checkCoverLookup advanceBalanced 728 (fun i => lookup boxTable074 i [])
      6 [] root074 tree074 = true := by decide +kernel

theorem originalCover074 :
    checkCover retainedDiagram boxes074 6 [] root074 tree074 = true := by
  apply lookup_cover_to_original advanceBalanced 728 (fun i => lookup boxTable074 i [])
    retainedDiagram boxes074 root074 tree074
  · decide +kernel
  · intro i
    exact lookup_eq_list boxTable074 boxes074 boxTable074_valid boxTable074_flat i []
  · exact advanceBalanced_eq
  · exact balancedCover074

#print axioms boxTable074_valid
#print axioms boxTable074_flat
#print axioms balancedCover074
#print axioms originalCover074

end Snake9.Shared89
