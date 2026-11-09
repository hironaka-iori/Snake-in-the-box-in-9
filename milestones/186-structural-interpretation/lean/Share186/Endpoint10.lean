import Share186.EndpointData
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Snake9.LocalWindow.ShareWindow185
open Snake9.LocalWindow.Tags Snake9.LocalWindow.Tags185
theorem ep_pos10 : epLits10.all (posE meaningDirect) = true := by decide +kernel
theorem ep_map10 : epLits10.map (vl meaningDirect) = epVerts10 := by decide +kernel
#print axioms ep_pos10
#print axioms ep_map10
end Snake9.LocalWindow.ShareWindow185
