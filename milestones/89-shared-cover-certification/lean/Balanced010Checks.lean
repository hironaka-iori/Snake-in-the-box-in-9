import Balanced010Data
import BalancedGraphChecks
import LookupCover

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Snake9.Shared89
open Snake9.Boxes88 Snake9.Certificate88 Snake9.Balanced89

theorem boxTable010_valid : check boxTable010 = true := by decide +kernel

theorem boxTable010_flat : flatten boxTable010 = boxes010 := by decide +kernel

theorem balancedCover010 :
    checkCoverLookup advanceBalanced 617 (fun i => lookup boxTable010 i [])
      6 [] root010 tree010 = true := by decide +kernel

theorem originalCover010 :
    checkCover retainedDiagram boxes010 6 [] root010 tree010 = true := by
  apply lookup_cover_to_original advanceBalanced 617 (fun i => lookup boxTable010 i [])
    retainedDiagram boxes010 root010 tree010
  · decide +kernel
  · intro i
    exact lookup_eq_list boxTable010 boxes010 boxTable010_valid boxTable010_flat i []
  · exact advanceBalanced_eq
  · exact balancedCover010

#print axioms boxTable010_valid
#print axioms boxTable010_flat
#print axioms balancedCover010
#print axioms originalCover010

end Snake9.Shared89
