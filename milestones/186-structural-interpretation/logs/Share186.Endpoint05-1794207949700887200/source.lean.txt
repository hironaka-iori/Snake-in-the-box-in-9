import Share186.EndpointData
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Snake9.LocalWindow.ShareWindow185
open Snake9.LocalWindow.Tags Snake9.LocalWindow.Tags185
theorem ep_pos5 : epLits5.all (posE meaningDirect) = true := by decide +kernel
theorem ep_map5 : epLits5.map (vl meaningDirect) = epVerts5 := by decide +kernel
#print axioms ep_pos5
#print axioms ep_map5
end Snake9.LocalWindow.ShareWindow185
