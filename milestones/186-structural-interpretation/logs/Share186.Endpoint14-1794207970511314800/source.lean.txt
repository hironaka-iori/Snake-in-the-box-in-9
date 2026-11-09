import Share186.EndpointData
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Snake9.LocalWindow.ShareWindow185
open Snake9.LocalWindow.Tags Snake9.LocalWindow.Tags185
theorem ep_pos14 : epLits14.all (posE meaningDirect) = true := by decide +kernel
theorem ep_map14 : epLits14.map (vl meaningDirect) = epVerts14 := by decide +kernel
#print axioms ep_pos14
#print axioms ep_map14
end Snake9.LocalWindow.ShareWindow185
