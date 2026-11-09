import Share186.EndpointData
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Snake9.LocalWindow.ShareWindow185
open Snake9.LocalWindow.Tags Snake9.LocalWindow.Tags185
theorem ep_pos7 : epLits7.all (posE meaningDirect) = true := by decide +kernel
theorem ep_map7 : epLits7.map (vl meaningDirect) = epVerts7 := by decide +kernel
#print axioms ep_pos7
#print axioms ep_map7
end Snake9.LocalWindow.ShareWindow185
