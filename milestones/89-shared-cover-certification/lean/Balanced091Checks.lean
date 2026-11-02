import Balanced091Data
import BalancedGraphChecks
import LookupCover

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Shared89
open Snake9.Boxes88 Snake9.Certificate88 Snake9.Balanced89

theorem boxTable091_valid : check boxTable091 = true := by decide +kernel

theorem boxTable091_flat : flatten boxTable091 = boxes091 := by decide +kernel

theorem balancedCover091 :
    checkCoverLookup advanceBalanced 785 (fun i => lookup boxTable091 i [])
      6 [] root091 tree091 = true := by decide +kernel

theorem originalCover091 :
    checkCover retainedDiagram boxes091 6 [] root091 tree091 = true := by
  apply lookup_cover_to_original advanceBalanced 785 (fun i => lookup boxTable091 i [])
    retainedDiagram boxes091 root091 tree091
  · decide +kernel
  · intro i
    exact lookup_eq_list boxTable091 boxes091 boxTable091_valid boxTable091_flat i []
  · exact advanceBalanced_eq
  · exact balancedCover091

#print axioms boxTable091_valid
#print axioms boxTable091_flat
#print axioms balancedCover091
#print axioms originalCover091

end Snake9.Shared89
