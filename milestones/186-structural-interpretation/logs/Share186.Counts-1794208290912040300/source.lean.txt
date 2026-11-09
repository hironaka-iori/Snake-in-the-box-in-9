import Share186.Endpoint00
import Share186.Endpoint01
import Share186.Endpoint02
import Share186.Endpoint03
import Share186.Endpoint04
import Share186.Endpoint05
import Share186.Endpoint06
import Share186.Endpoint07
import Share186.Endpoint08
import Share186.Endpoint09
import Share186.Endpoint10
import Share186.Endpoint11
import Share186.Endpoint12
import Share186.Endpoint13
import Share186.Endpoint14
import Share186.Endpoint15
import Share186.Endpoint16
import Share186.Endpoint17
import Share186.EndpointSorted
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Snake9.LocalWindow.ShareWindow185
open Snake9.LocalWindow.Tags Snake9.LocalWindow.Tags185
theorem ep_positive : epLits.all (posE meaningDirect) = true := by
  simp only [epLits,List.all_append,ep_pos0,ep_pos1,ep_pos2,ep_pos3,ep_pos4,ep_pos5,ep_pos6,ep_pos7,ep_pos8,ep_pos9,ep_pos10,ep_pos11,ep_pos12,ep_pos13,ep_pos14,ep_pos15,ep_pos16,ep_pos17,Bool.and_self]
theorem ep_mapping : epLits.map (vl meaningDirect) = epVerts := by
  simp only [epLits,epVerts,List.map_append,ep_map0,ep_map1,ep_map2,ep_map3,ep_map4,ep_map5,ep_map6,ep_map7,ep_map8,ep_map9,ep_map10,ep_map11,ep_map12,ep_map13,ep_map14,ep_map15,ep_map16,ep_map17]
theorem counts_ok : ctrs.all (ctrOK meaningDirect (centresK window bounds)) = true := by
  have hb : epLits.all (baseOK meaningDirect) = true := by
    apply List.all_eq_true.mpr
    intro a ha
    have hp := List.all_eq_true.mp ep_positive a ha
    simp only [posE,Bool.and_eq_true] at hp
    simp [baseOK,hp.1.2,hp.2]
  rw [endpoint_counter_data]
  simp only [List.all_cons,List.all_nil,Bool.and_true,ctrOK]
  simp only [hb,ep_positive,ep_mapping,ep_sorted,beq_self_eq_true,Bool.and_self]
#print axioms counts_ok
end Snake9.LocalWindow.ShareWindow185
