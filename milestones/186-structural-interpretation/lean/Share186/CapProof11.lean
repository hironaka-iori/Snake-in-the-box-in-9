import Share186.CapJoin70
import Share186.CapJoin71
import Share186.CapData
import Share186.CapBase00
import Share186.CapBase01
import Share186.CapBase02
import Share186.CapBase03
import Share186.CapBase04
import Share186.CapBase05
import Share186.CapBase06
import Share186.CapBase07
import Share186.CapBase08
import Share186.CapBase09
import Share186.CapBase10
import Share186.CapBase11
import Share186.CapBase12
import Share186.CapBase13
import Share186.CapBase14
import Share186.CapBase15
import Share186.CapBase16
import Share186.CapBase17
import Share186.CapBase18
import Share186.CapBase19
import Share186.CapBase20
import Share186.CapBase21
import Share186.CapBase22
import Share186.CapBase23
import Share186.CapBase24
import Share186.CapBase25
import Share186.CapBase26
import Share186.CapBase27
import Share186.CapBase28
import Share186.CapBase29
import Share186.CapBase30
import Share186.CapExtra00
import Share186.CapExtra01
import Share186.CapExtra02
import Share186.CapLemmas
import Share186.CapProof00
import Share186.CapProof01
import Share186.CapProof02
import Share186.CapProof03
import Share186.CapProof04
import Share186.CapProof05
import Share186.CapProof06
import Share186.CapProof07
import Share186.CapProof08
import Share186.CapProof09
import Share186.CapProof10
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Snake9.LocalWindow.ShareWindow185
open Snake9.LocalWindow.Tags Snake9.LocalWindow.Tags185
theorem total71_ok : totOK meaningDirect smeaningDirect window (centresK window bounds) (tots.getD 71 dfltTot) = true := by
  have hu : (capBaseLits ++ capExtraLits).all (posU meaningDirect smeaningDirect) = true := by simp only [List.all_append,capBase_pos,capExtra_pos,Bool.and_self]
  have hp : (capBasePairs ++ capExtraPairs).isPerm (capL (centresK window bounds) capSpec15) = true := by
    apply pair_isPerm_of_perm
    rw [capBase_rows,capExtra_rows,cap15_rows]
    exact threshold_layers_perm capCorners
  rw [cap71_data]
  simp only [totOK,base_of_posU _ hu,hu,List.map_append,capBase_map,capExtra_map,hp,spec15_ok,Bool.and_self]

#print axioms total71_ok
end Snake9.LocalWindow.ShareWindow185
