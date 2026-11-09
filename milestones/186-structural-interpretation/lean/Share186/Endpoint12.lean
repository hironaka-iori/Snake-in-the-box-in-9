import Share186.EndpointData
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Snake9.LocalWindow.ShareWindow185
open Snake9.LocalWindow.Tags Snake9.LocalWindow.Tags185
theorem ep_pos12 : epLits12.all (posE meaningDirect) = true := by decide +kernel
theorem ep_map12 : epLits12.map (vl meaningDirect) = epVerts12 := by decide +kernel
#print axioms ep_pos12
#print axioms ep_map12
end Snake9.LocalWindow.ShareWindow185
