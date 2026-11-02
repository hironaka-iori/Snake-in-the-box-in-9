import Balanced101Data
import BalancedGraphChecks
import LookupCover

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Shared89
open Snake9.Boxes88 Snake9.Certificate88 Snake9.Balanced89

theorem boxTable101_valid : check boxTable101 = true := by decide +kernel

theorem boxTable101_flat : flatten boxTable101 = boxes101 := by decide +kernel

theorem balancedCover101 :
    checkCoverLookup advanceBalanced 672 (fun i => lookup boxTable101 i [])
      6 [] root101 tree101 = true := by decide +kernel

theorem originalCover101 :
    checkCover retainedDiagram boxes101 6 [] root101 tree101 = true := by
  apply lookup_cover_to_original advanceBalanced 672 (fun i => lookup boxTable101 i [])
    retainedDiagram boxes101 root101 tree101
  · decide +kernel
  · intro i
    exact lookup_eq_list boxTable101 boxes101 boxTable101_valid boxTable101_flat i []
  · exact advanceBalanced_eq
  · exact balancedCover101

#print axioms boxTable101_valid
#print axioms boxTable101_flat
#print axioms balancedCover101
#print axioms originalCover101

end Snake9.Shared89
