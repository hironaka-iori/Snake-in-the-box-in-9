import Share186.EndpointData
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Snake9.LocalWindow.ShareWindow185
open Snake9.LocalWindow.Tags Snake9.LocalWindow.Tags185
theorem ep_pos6 : epLits6.all (posE meaningDirect) = true := by decide +kernel
theorem ep_map6 : epLits6.map (vl meaningDirect) = epVerts6 := by decide +kernel
#print axioms ep_pos6
#print axioms ep_map6
end Snake9.LocalWindow.ShareWindow185
